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

## 進捗 (2026-07-19): **Cor 1.6 を Thm 1.5 から sorry-free で導出** — 残 sorry は Thm 1.5 のみ

`oPiCore_isSylow_or_isThreeStepGroup` (Cor 1.6) は**もう sorry ではない**。Gorenstein の
「as an immediate corollary」を実際に形式化し、Thm 1.5 の 3 ケースを分岐して導出した (全 case が
本物の議論を要した — 「immediate」は書籍の省略):

- **(i) `G` 冪零** → `N = ⊤` で下記 index 補題。
- **(ii) `G` が核 `F(G)` の Frobenius 群** → `[G : F(G)] = |A|` (`IsComplement'.index_eq_card`) が
  `|F(G)|` と互いに素 (`coprime_card_kernel_complement`)、かつ `1 ≠ O_p(G) ≤ F(G)` ゆえ `p ∣ |F(G)|`
  ⟹ `p ∤ [G : F(G)]`。
- **(iii) `G` が素数 `q` に関する 3-step 群** → `q = p`。`q ≠ p` なら `O_p(G) ≤ O_{q'}(G) = ⊥`
  (既証の `oPiCore_pPrime_eq_bot`) が `O_p(G) ≠ ⊥` に矛盾。

新規の共有ステップ (**axiom-clean**、AxiomsCheck 登録済):
`exists_sylow_eq_oPiCore_of_isNilpotent_normal_of_not_dvd_index` — 有限群 `G` が冪零正規部分群 `N`
を持ち `p ∤ [G:N]` なら `O_p(G)` は Sylow `p`。(`N` の Sylow `p` が `G` の Sylow でもあり、`N` 冪零
ゆえ `N` で characteristic、`N ⊴ G` ゆえ `G` で正規、正規 `p`-部分群として `O_p(G)` に入り、
`O_p(G)` 自身が `p`-群なので Sylow の極大性で一致。)

## 進捗 (2026-07-19 続き): **Thm 1.5 step 2 を sorry-free で証明** + 階層移設 2 件

### 階層移設 (commit `1adb7cc60`) — 旧ブロッカー 1 を解消

汎用有限群論 2 件が BG 配下に埋まって shared infra から使えなかったので移設 (alias 無し・全
call site repoint・全 leaf build green):

- `centralizer_fitting_le_fitting` (P. Hall) → 新 `OddOrder/GroupTheory/FittingSelfCentralizing.lean`
- `commute_of_coprime_orderOf_of_isNilpotent` → 新 `OddOrder/GroupTheory/NilpotentCoprimeCommute.lean`

### Thm 1.5 step 2 (`not_commute_of_coprime_orderOf_card_fitting`) — **axiom-clean**

> 可解 CN 群で、位数が `|F(G)|` と互いに素な元は `F(G)` の非単位元を一切中心化しない。

= 原文の「`A` は `F` に regular に作用し `FA` は Frobenius 群」。**CN 仮説 (Lemma 1.2) が実際に
効く箇所**。証明は原文の 4 手:

1. Lemma 1.2 で `y'` が Sylow `p` 全体、したがって `O_p(G)` を中心化。
2. `C_G(x')` は CN 仮説で冪零、かつ `F` の位数 `p`-prime な元を全て含む (`F` 冪零)。
3. その冪零中心化群の中で位数互いに素 ⟹ 可換。
4. `F` は Sylow 部分群で生成される (`iSup_default_sylow_eq_top_of_nilpotent`) ので `y'` は `F`
   全体を中心化 ⟹ `C_G(F) ≤ F` で `y' ∈ F` ⟹ `q ∣ |F|` で矛盾。

⚠ **原文より一般形**: Gorenstein は Hall `π(F)'`-部分群 `A` の元について述べるが、証明が使うのは
「位数が `|F|` と互いに素」だけなので**単一の元について**述べた (弱化でなく一般化。`A` 版は各元に
適用すれば従う)。

付随して axiom-clean で証明: `sylow_fitting_map_le_oPiCore` (`F(G)` の Sylow `p` は `O_p(G)` 内) /
`commute_of_mem_fitting_of_coprime_orderOf` / `orderOf_mk_eq`。

### Thm 1.5 step 3 (`exists_sylow_eq_oPiCore_of_normal_pPrime_le_fitting`) — **axiom-clean**

> CN 群で `O_p(G) ≠ 1` かつ `F(G)` が位数 `p`-prime な非自明正規部分群 `N` を含むなら、
> `O_p(G)` は既に Sylow `p`。

= 原文が「`G ⊋ FA` なら `π(F)` は単一素数」を示す論法 (`N = O_{p'}(F)` で適用)。
1. `O_p(G)` が `N` を中心化 (両者冪零 `F(G)` 内・位数互いに素) → 2. Lemma 1.2 で Sylow `p` 全体に
格上げ → 3. `C = C_G(N)` は正規かつ冪零 → 4. `P` は冪零 `C` の Sylow ゆえ char → `G` で正規 →
5. 正規 `p`-部分群は `O_p(G)` 内ゆえ `P = O_p(G)`。
⚠ **原文より一般形**: 書籍の可解性仮定は論法が使わないので落とした。

### 残 sorry は 1 件 = **Thm 1.5** (`solvableCN_nilpotent_or_frobenius_or_threeStep`)

可解 CN 群は「冪零 ∨ 核 `F(G)` の Frobenius ∨ ある素数に関する 3-step」。**step 2 / step 3 は済**。
残りは:

0. ~~**step 1 (setup) の組み立て**~~ — **2026-07-19 完了** (3 件とも axiom-clean):
   `isNilpotent_of_fitting_eq_top` (case i) / `conj_ne_of_isHallSubgroup_fitting_pPrime`
   (Hall `π(F)'`-部分群が `F(G)` 上に固定点なしで作用 = step 2 を `conj_frobenius` の形に包む) /
   `isFrobeniusGroup_fitting_of_isComplement` (case ii への橋渡し)。
   ⟹ **repo の道具だけで書ける部分は step 1/2/3 で出揃った**。
1. **`A` の冪零性** — Gorenstein Thm 10.3.1(iv)(v) (位数 `qr` の部分群は巡回 / metacyclic 補群)
   が **不在** (`IsMetacyclic` はあるが Frobenius 理論と未接続)。ここが load-bearing。
   ⚠ 奇数位数なら `Ch06.isZGroup_of_isFrobeniusAction_of_odd` が使えるので、**BG App.D が要求する
   のは奇数位数の場合だけ**である点を着手時に再評価する価値あり (原文の偶数位数分岐 =
   `unique_involution` は repo に在る)。
2. ~~**`π(F)` が単一素数**~~ — **step 3 として 2026-07-19 完了**
   (`exists_sylow_eq_oPiCore_of_normal_pPrime_le_fitting`)。
3. **最終ステップ** (`P` が `Ā` に regular に作用 ⟹ `PA` Frobenius) — Gorenstein Lemma 10.1.3
   (fpf 自己同型が `K/F` に降りる) が **不在**。
4. Gorenstein Thm 1.3.1(ii) (全 Sylow が巡回 or 四元数 ⟹ 構造) — **不在**。
   ⚠ **Cor 1.6 には不要** — 下記「book-strength 債務」を解消するときだけ要る。

**D.1 は未着地ゆえ `AppD_CNGroups.lean` は無変更**。

## 進捗 (2026-07-19 その3): **「`A` の冪零性」のブロッカーは幻だった — 完全な経路を確定**

### 実測でわかったこと (3 度目の stale "不在" ラベル)

**Gorenstein Thm 10.3.1(v)「`A` の位数 `pq` の部分群は巡回」は repo に既にある**:
`OddOrder.Isaacs.Ch06.false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime`
(`FrobeniusGroup.lean:1204`、**Isaacs Thm 6.9**) — 「Frobenius actor は位数 `p*q` の非巡回部分群を
含み得ない」= (v) の対偶。descriptive 名で grep しなかったための取りこぼし。
本 issue でこれが **3 件目**の誤 "不在" (先の 2 件 = Gorenstein Thm 5.3.5、`C_G(F) ≤ F` の配置)。

⚠ また **Gorenstein Ch.10 に (v) の証明本体は無い** (Thm 3.1 の Proof は偶数位数の (vi) だけを示し、
(iv)(v) は Thm 2.7.6 / 5.3.14 / 5.4.11 / 7.6.2 に引用で丸投げ)。原文を追う方針だと Ch.5 まで
遡ることになるが、**Isaacs 経由で既に repo にある**ので不要。

### 確定した経路 (metacyclic も Thm 1.3.1(ii) も不要)

`A` = Hall `π(F)'`-部分群 (= `F(G)` 上の Frobenius 補群、step 2 で確立済) が冪零であることの証明:

1. `A` の位数が奇なら Z-群 (全 Sylow 巡回) — `Ch06.isZGroup_of_isFrobeniusAction_of_odd` ✅ repo
2. `A' = 1` なら `A` 可換 ⟹ 冪零。以下 `A' ≠ 1`。
3. mathlib `IsZGroup.coprime_commutator_index` (`gcd(|A'|, [A:A']) = 1`) +
   `IsZGroup.isCyclic_commutator` (`A'` 巡回) ✅ mathlib
   ⟹ `q ∣ |A'|` を取ると **`A'` の Sylow `q` は `A` の Sylow `q`** かつ `A'` で char ゆえ `A` で正規。
4. `Ω₁(Q)` は `Q` で char ⟹ `A` で正規。他の素数 `r` と Sylow `R` について `Ω₁(Q)Ω₁(R)` は
   位数 `qr` の部分群 ⟹ **Isaacs Thm 6.9 (上記) で巡回** ⟹ `Ω₁(Q)` が `Ω₁(R)` を中心化。
5. **Lemma 1.2** (既証) ⟹ `Q` が `R` を中心化。全ての `r` について成り立ち `Q` 自身可換ゆえ
   `Q ≤ Z(A)`、`Q ≠ 1`。
6. `isNilpotent_of_centerIn_ne_bot` (下記、2026-07-19 追加) ⟹ **`A` 冪零**。

⟹ **旧ブロッカー 1 (`A` の冪零性) は新規前提ゼロで書ける**。metacyclic (Thm 7.6.2) も
Thm 1.3.1(ii) も経路上に不要 (Gorenstein は metacyclic 経由で `Ω₁(Q) ⊴ A` を得るが、
mathlib の Z-群 API で `A'` 経由の方が短い)。

### 追加した補題 (**axiom-clean**、AxiomsCheck 登録済)

`isNilpotent_of_centerIn_ne_bot` — CN 群で中心が非自明な部分群は冪零 (`1 ≠ z ∈ Z(A)` について
`A ≤ C_G(z)` で `C_G(z)` は CN 仮説より冪零)。上記 step 6。

### 残ブロッカーは 1 件のみ

**Gorenstein Lemma 10.1.3** (fpf 自己同型が `K/F` に降りる) — 最終ステップ (`P` が `Ā` に regular に
作用 ⟹ `PA` Frobenius ⟹ 3-step) で load-bearing。**着手前に必ず実測せよ** — 本 issue の "不在"
ラベルは 3/4 が誤りだった。`Isaacs/Ch06_FrobeniusActions/` と
`BG/Ch1_Preliminary/S03c_Thm37.lean` (`kernel_acts_trivially_of_coprime_fixedPointFree`,
`chiefFactor_fixedPointFree`) を descriptive 名で先に grep すること。

### 次の着手 (2026-07-19 時点)

**上記「確定した経路」の step 1-6 を Lean で書く**。新規前提は不要で、必要な部品は全て
repo / mathlib にある。実装上の主な手間は `Ω₁(Q)Ω₁(R)` の位数 `qr` の部分群としての扱い
(`Ω₁(Q) ⊴ A` ゆえ積が部分群、位数は `q * r`) と Sylow の char 性の transport。

その後に残るのは Gorenstein Lemma 10.1.3 のみ (上記のとおり要実測)。

### ⚠ 旧ブロッカーリストの訂正 (2026-07-19、実測)

旧リストの項目 2「Gorenstein Thm 5.3.5 (互いに素な作用 `K = [R,K]·C_K(R)`) — **不在**」は
**二重に誤り**だった:

1. **repo に在る**: `OddOrder.BG.Ch3.S13.subgroup_coprime_decomposition`
   (`S13_PrimeAction.lean:749`、BG Prop 1.6(d) = Isaacs Thm 4.34 の subgroup 形)。
   descriptive 名で grep しなかったための取りこぼし ([[verify-port-state-by-number-not-coq-name]])。
2. **そもそも Thm 1.5 の証明が使っていない**。原文 (`finite-groups.pdftotext.txt` L21600-21650) を
   逐語で読むと、使うのは Thm 6.1.3 / Thm 6.4.1(i) / Lemma 1.2 / Thm 10.3.1(iv)(v)(vi) / Thm 7.6.2 /
   Thm 1.3.1(ii) / Lemma 10.1.3 のみ。

⟹ 「不在」ラベルは着手前に必ず実測し直す。**原文の証明を読んでから依存を列挙する**。

### book-strength 債務 (新規記録)

Thm 1.5 の clause (ii) について、原文は補群を「巡回 ∨ (奇数位数巡回 × 一般四元数)」まで確定するが、
Lean の statement は「核が `F(G)` の Frobenius 群」までに留めた。理由: repo に
`IsGeneralizedQuaternion` が無く、かつ Cor 1.6 はこの精緻化を消費しないため
(sorry を必要以上に強くしない = conservative)。上記ブロッカー 3 と同時に解消する。

⚠ **優先順位の訂正 (2026-07-18、番号は 07-19 の再採番に合わせて読み替え)**: 一時「配置問題 (1) を
直せばブロッカーが減る」と書いたがこれは**誤解を招く数え方**だった。残る 2/3/4 は実質的な数学的欠落なので、**配置を直しても
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

## 進捗 (2026-07-19 その4): **Thm 1.5 の完全な証明経路を確定 — 残ブロッカー 0**

原文精読 + 実測で、**Gorenstein の行間 (Ā ⊴ Ḡ の暗黙の前提) を埋める完全経路**を確定した。
「`A` の冪零性」は経路から消滅 (直接巡回性へ)、Lemma 10.1.3 は初等 (~25 行) と判明。

### 原文の行間 (重要な発見)

Thm 1.5 末尾の「P̄ が Ā に regular に作用 ⟹ P̄Ā Frobenius」は **Ā ⊴ Ḡ を暗黙に前提**する
(regular 作用には正規性が要る; 抽象的には反例あり — S₄ = Ḡ, p=3, Ā=D₈ は「可解 + O_p=1 +
冪零 Hall p' + p/p' 非可換」を全て満たすが Ā ⋬ Ḡ)。埋める経路 = **|A| 奇 ⟹ A 巡回 ⟹
N̄ := O_{p'}(Ḡ) 巡回 ⟹ Aut(N̄) 可換 ⟹ Ḡ' ≤ C_Ḡ(N̄) ≤ N̄ ⟹ Ḡ/N̄ 可換 ⟹ Ā ⊴ Ḡ**。

### 確定経路 (使用部品は全て実在確認済)

0. **(i)**: `Group.IsNilpotent G` なら終了。以下 G 非冪零、`F := fitting G ≠ ⊥`
   (`fitting_ne_bot_of_solvable_nontrivial`)、`A` = Hall π(F)' (`hall_exists_of_piSeparable`)。
1. **(†)**: F が p-群のとき、p'-元 x ≠ 1 は p-元 k ≠ 1 と可換になれない。
   [r ∣ ord x を取り x' := x^(ord x/r)、Lemma 1.2 (P = Sylow ∋ k, Q = ⟨x'⟩) ⟹ x' が
   Sylow p 全体を中心化 ⟹ F ≤ Sylow (正規 p-部分群) ⟹ x' ∈ C(F) ≤ F ⟹ r = p ✗]
2. **(‡) = Lemma 10.1.3 の適用**: Ḡ := G/F で「mk a (a ∈ A, mk a ≠ 1, p ∤ ord a) は Ḡ の
   非自明 p-元 ū と非可換」。[K := comap mk' ⟨ū⟩ は p-群 (`IsPGroup.comap_of_ker_isPGroup`)、
   a は (†) より K に fpf 作用、**新補題 L1** (fpf は商に降りる、coset 形:
   `k⁻¹(xkx⁻¹) ∈ F → k ∈ F`、twisted map 全単射で ~25 行) ⟹ ū = 1 ✗]
3. **G = FA なら (ii)**: `isFrobeniusGroup_fitting_of_isComplement` (済)。
4. **G ⊋ FA なら π(F) = {p}**: |π| ≥ 2 と仮定 → 各 p ∈ π で N := (F の Sylow r, r ≠ p) は
   `O_r(G) ≠ ⊥` を与え step 3 (`exists_sylow_eq_oPiCore_of_normal_pPrime_le_fitting`、済) で
   `O_p(G)` Sylow ⟹ F が Hall π ⟹ |F||A| = |G| = |FA| ✗。以降 F = O_p(G) は p-群、A は
   Hall p'、A ≠ ⊥ (さもなくば G は p-群で冪零 ✗ `IsPGroup.isNilpotent`)。
5. **|A| 奇**: 2 ∣ |A| なら t ∈ A involution (Cauchy)。**新補題 L3**: fpf involution は
   F を反転 (twisted map 全射) ⟹ ∀g, ⁅t,g⁆ が F を中心化 (計算) ⟹ ⁅t,g⁆ ∈ C(F) ≤ F ⟹
   **mk t ∈ Z(Ḡ)**。p ∣ |Ḡ| (G ⊋ FA) の p-元と可換 ⟹ (‡) ✗。
6. **A 巡回**: `isZGroup_of_isFrobeniusAction_of_odd` + Isaacs 6.19
   (`existsUnique_card_prime_of_isFrobeniusAction_of_odd` / `normal_of_card_prime_...` —
   **OddComplement.lean に既存**、冪零性ステップ丸ごと不要) ⟹ 相異なる素数 q,r の唯一の
   位数-q/r 部分群 R_q, R_r ⊴ A は可換 (`commute_of_normal_of_disjoint`) ⟹ **Lemma 1.2** で
   A の Sylow q × Sylow r が元ごと可換 (R_q ≤ 全 Sylow q) ⟹ C_A(Q₀) が全素数の Sylow を含み
   `eq_top_of_forall_exists_sylow_le` ⟹ Q₀ ≤ Z(A) ⟹ `centerIn ≠ ⊥` ⟹
   `isNilpotent_of_centerIn_ne_bot` + mathlib instance `IsZGroup + IsNilpotent → IsCyclic`。
7. **Ā ⊴ Ḡ**: N̄ := O_{p'}(Ḡ) ≠ ⊥ [O_p(Ḡ) = ⊥ (comap は正規 p-群 ≤ F) ⟹ F(Ḡ) は p'-群]、
   N̄ ≤ Ā (Hall 極大性)、N̄ 巡回 (≤ Ā ≅ A)。C_Ḡ(N̄) は (‡) より p-元なし ⟹ p'-正規 ⟹ ≤ N̄。
   `IsCyclic.mulAutMulEquiv` (Aut 可換) ⟹ Ḡ' ≤ C_Ḡ(N̄) ≤ N̄ ⟹ Ḡ/N̄ 可換 ⟹ Ā ⊴ Ḡ ⟹
   **Ā = N̄** (正規 p'-群 ≤ O_{p'})。
8. **IsThreeStepGroup 組み立て**: 条件1 = FA (= comap N̄ = F ⊔ A) 上の Frobenius (kernel F,
   complement A subgroupOf, fpf = step 2 済, 巡回 ✓ 奇 ✓)。条件2a = G/FA が p-群 ([G:FA] は
   p-冪) ⟹ `opPPrimePCore_eq_top_iff`。条件2b = FA ≠ ⊤ ✓。条件3 = Ḡ Frobenius kernel
   Ā = N̄, complement P̄ (Sylow p of Ḡ; `isComplement'_iff_card_mul_and_disjoint`,
   conj_frobenius = (‡))。

### 実装レイアウト

- **新 leaf** `OddOrder/GroupTheory/FixedPointFreeConjugation.lean` (~180 行):
  twisted-map 全単射 + L1 (fpf 商降下 = Gorenstein Lemma 10.1.3 coset 形) + L3
  (involution 反転 + `⁅t,g⁆ ∈ centralizer F`)。generic (CN 非依存)。
- **CNGroupStructure.lean 追記** (~400 行): (†) / (‡) / A-巡回性 / Thm 1.5 本体。
  1500 行接近時は hub に分割委任。

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

## 進捗 (2026-07-19 その5): **Thm 1.5 完全証明 — leaf 全体が sorry-free (tier 1 の Cor 1.6 まで完了)**

`solvableCN_nilpotent_or_frobenius_or_threeStep` (Gorenstein Ch.12 §1 Theorem 1.5) を「その4」の
確定経路どおりに実証明した。`CNGroupStructure.lean` は **sorry 0**、主要宣言は全て axiom-clean
(`#print axioms` 実測: propext / Classical.choice / Quot.sound のみ)。AxiomsCheck に
Thm 1.5 / Cor 1.6 / fpf toolbox / (†)(‡) / 巡回性 / endgame helpers の 17 エントリを追加登録。

### 実装で経路から乖離した点 (記録)

1. **「Ā ⊴ Ḡ」の Aut-可換ステップ**は `IsCyclic.mulAutMulEquiv` (mathlib) 経由で
   `commutatorElement_mem_centralizer_of_isCyclic_normal` として一般補題化 (生成元の zpow 計算不要)。
2. **quotient 型を跨ぐ rewrite は motive 崩壊で不可能** (`G ⧸ M` の group instance に埋まる
   `Normal` instance 項が subgroup を部分項に持たないため)。`O_p(G) = F(G)` を通す転送は
   **変数部分群 + `subst` + proof irrelevance** の congruence lemma 2 件
   (`comap_oPiCore_quotient_congr` / `exists_isFrobeniusGroup_map_quotient_congr`) で実施。
   同型パターンの再利用可能な技法 (メモリの instance-trap 系列に該当)。
3. 新規汎用 helpers: `mulEquivMapOfInfKerEqBot` (ker と交わらない部分群は像と同型) /
   `isFrobeniusGroup_subgroupOf_sup` (fpf 作用 ⟹ `A ⊔ F` 上の Frobenius 構造)。

### 残債務 (いずれも本 issue 記載済みの follow-up、Cor 1.6 の消費はブロックしない)

- **book-strength 債務**: Thm 1.5 clause (ii) の補群精緻化 (巡回 ∨ 奇巡回×一般四元数) —
  `IsGeneralizedQuaternion` 不在のため見送り (Gorenstein Thm 1.3.1(ii) が必要)。
- **非空性監査の穴**: 3-step 群の Lean witness (`F_{3⁶} ⋊ (C₇ ⋊ C₃)`) 未構成。

### 次の着手 = tier 1 残り: BG App.D で Cor 1.6 を消費して D.1 → D.2 を閉じる

⚠ 申し送りどおり、AppD が Cor 1.6 を消費すると `GroupTheory` leaf ← `AppD` の循環になるため、
**着手時に `IsCNGroup` を `CNGroupStructure.lean` へ移設**すること (Lemma 1.2 の展開形仮説と
定義的に同一)。また `CNGroupStructure.lean` は 1865 行 (>1500 trigger) — 凍結 prefix
(cores + `IsThreeStepGroup` + BG 消費帰結) を `ThreeStepGroup.lean` へ分割予定。

---

## ✅ 消費側も完了 (2026-07-19): BG App.D D.1/D.2 が sorry-free

本 issue の成果 (Thm 1.5 → Cor 1.6) を実際に消費して **BG App.D の D.1/D.2 を証明**した
(issue 3020 が正本)。その過程で 3-step 群の帰結を 1 つ追加:

**`IsThreeStepGroup.inf_sylow_eq_oPiCore`** (`GroupTheory/ThreeStepGroup.lean`) —
3-step 群では相異なる Sylow p-部分群の交わりがちょうど `O_p(G)`。
BG App.D が「3-step 群の定義と short argument から」で済ませる display (D.2) の一般形。

証明の骨 (全 6 宣言 axiom-clean、AxiomsCheck 登録済):
- `sylow_inf_opPPrimeCore_eq_oPiCore` (任意の有限群): `S ∩ O_{p,p'}(G) = O_p(G)`
- `sylow_sup_eq_top_of_isPGroup_quotient` (任意の有限群): `G/N` が p-群なら `S ⊔ N = ⊤`
- ⟹ `isComplement'_quotient_sylow` → `isFrobeniusGroup_quotient_sylow`
  (補群であれば自動的に Frobenius 補群 — Frobenius 条件は核だけで書けるので
  定義が与える補群 `B` から Isaacs Thm 6.4 (4)⇒(1) で任意の Sylow 像へ移せる)
- Frobenius 補群は TI (Isaacs Thm 6.4 (1)⇒(2)) → comap で引き戻す

また `oPiCore_le_sylow` (正規 p-部分群は全 Sylow に入る) を public 化
(同内容が 2 ファイルで `private` に重複していた)。

**本 issue の残債は「Thm 1.3.1(ii) による clause (ii) の補群の細分」のみ** (Cor 1.6 には不要)。
