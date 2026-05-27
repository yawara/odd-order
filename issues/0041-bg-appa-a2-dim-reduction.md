---
id: 41
slug: bg-appa-a2-dim-reduction
title: "BG App.A A.2 / Gorenstein 3.8.1 次元縮約 (char-p 二次既約 ⇒ dim V = 2)"
created: 2026-05-28
---

# BG App.A A.2 / Gorenstein 3.8.1 次元縮約 (char-p 二次既約 ⇒ dim V = 2)

> **この issue は単独で読めるように書いてある**(別セッション引き継ぎ用)。前提知識ゼロから着手できる。

## 背景 — なぜこれが要るか

Feit–Thompson(奇数位数定理)の Lean 形式化プロジェクト。BG (Bender–Glauberman,
_Local Analysis for the Odd Order Theorem_) の局所解析パートを形式化中。その核心に
**BG Thm 6.2 (Glauberman の normal-J / Z(J) 定理)** = `Z(J(S))·O_{p'}(G) ⊴ G` があり、
§7–§9 (Uniqueness) で 7+ 箇所引用される。

問題: **本プロジェクトは Gorenstein 1968 "Finite Groups" を一次参照に使わない方針**
(CLAUDE.md。BG の "**G**, Thm X.Y.Z" 引用は Isaacs FGT の対応定理に読み替える)。ところが
**Isaacs FGT は Glauberman Z(J)-定理を明示的に省く**(Isaacs p.217)。⇒ Thm 6.2 は読み替え
不能。解決ルートとして **BG App.A (p-Stability) + App.B (Puig L(S))** を採る(設計決定:
[`notes/meta/bg_s6_appAB_route_2026_05_28.md`](../notes/meta/bg_s6_appAB_route_2026_05_28.md))。

2026-05-28 の kernel-connection spike で、そのルートの **唯一の実質的な数学的欠落** が
本 issue の対象だと判明した(同ノート **§0** 参照)。依存連鎖:

```
Thm 6.2 ⟸ App.B Thm B.4 ⟸ Thm A.5 ⟸ Thm A.4(c) ⟸ Thm A.3 ⟸ Thm A.2 ⟸ Thm A.1
                                                                    ↑
                                              ★ 本 issue = A.2 の「次元縮約パート」
```

- A.5, A.4, A.3 は A.2 の上に積む(reduction glue、別途)。
- **A.1**(dim-2 base)は部品が揃っている(下記「使える部品」)。
- **A.2 の証明本体 = Gorenstein 3.8.1 の「次元 2 への縮約」** が、Isaacs にも mathlib にも
  repo にも無い。BG App.A はこれを *"follow the proof of Theorem 3.8.1 of **G** up to page
  105, where V is shown to have dimension 2"* と書くだけで証明を書かない。**ここを Lean で
  自前形式化するのが本 issue**。

⚠️ よくある誤解(spike で訂正済): repo の `gl2_pSubgroup_centralizes_of_normalizes`
(Isaacs Lem 7.3)や `sylow_normal_of_elementary_normal_P_theorem`(Thm 7.5)は **この
次元縮約ではない**。7.3 は GL(2,p) の補題で reduced J(P) 経路 (7.5/7.6) 専用。7.5 の次元縮約は
`|V:C_V(P)| ≤ p` を**仮説に取る**(二次作用はそれを dim≤2 でしか満たさない、rank-nullity)。
詳細は上記ノート §0。**本 issue は別物の新規証明**。

## ターゲット(正確な statement)

### 主目標 = 次元縮約補題

BG Thm A.2 の証明本体。informal:

> `p` を奇素数、`F` を `F_p` の代数閉包、`V` を有限次元 `F`-ベクトル空間とする。
> `G ≤ GL(V)` が `V` 上 **忠実かつ既約** に作用し、`G` が **2 つの**「二次最小多項式を持つ
> `p`-元」で生成されているとする。ならば `dim_F V = 2`。

補足: 「二次最小多項式を持つ `p`-元」= `(ρ x - 1)² = 0` かつ `ρ x ≠ 1` な `x`。char `p` では
`(x-1)²=0 ⇒ x^p = 1`(`n := x-1`, `n²=0` ⇒ `x^p = (1+n)^p = 1 + p·n = 1`)なので自動的に
位数 `p` の元。⇒ 仮説は実質「`(ρx−1)²=0, ρx≠1`(`y` も)、`p` 奇、忠実既約、`G=⟨x,y⟩`」。

Lean signature 案(細部は実装者調整 — 既約の符号化と表現の型は要検討):

```lean
-- F = AlgebraicClosure (ZMod p) のような alg-closed char-p 体
theorem quadratic_two_generated_irreducible_finrank_eq_two
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    {G : Type*} [Group G] [Finite G] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hirr : IsSimpleModule (MonoidAlgebra F G) ρ.asModule)   -- ← 既約 (要確認: asModule の正確な綴り)
    (x y : G) (hgen : (⊤ : Subgroup G) = Subgroup.closure {x, y})
    (hx : (ρ x - 1) ^ 2 = 0) (hxne : ρ x ≠ 1)
    (hy : (ρ y - 1) ^ 2 = 0) (hyne : ρ y ≠ 1) :
    Module.finrank F V = 2 := by
  sorry
```

(`ρ x` は `Module.End F V` の元として扱う。`ρ x - 1` の `1` は `LinearMap.id`。`IsSimpleModule`
での既約符号化が扱いにくければ「`G`-不変部分空間は `⊥` か `⊤` のみ」で直書きしてよい。)

### A.2 本体(縮約 + A.1、follow-on)

`dim V = 2` が出たら A.2 は A.1 で閉じる:

> **A.2**: 上記仮説(忠実既約・二次 `p`-元 2 生成・`p` 奇)⇒ `|G|` は偶数。
> 証明: 縮約補題で `dim V = 2`。`G` は非自明 `p`-元を含むので `p ∣ |G|`。もし `|G|` 奇なら
> A.1 が `p ∤ |G|` を与え矛盾。∴ `|G|` 偶。

A.2 まで仕上げてくれてよいが、**最小の deliverable は次元縮約補題**(`= 2`)。A.1/A.2 の
assemble は短い follow-on。

## なぜ「二次」「二生成」「`p` 奇」が効くか(prover 向け orientation)

- **二生成が本質**。「二次 `p`-元で生成」だけでは dim は大きくできる: SL(`n`,`p`) は
  transvection(二次 `p`-元)で生成され、`n` 次元既約だが transvection は多数要る。
  **2 つだけ**だと既約に作用できるのは `dim ≤ 2` の場合に限られる、というのが縮約の心臓部。
- **`p` 奇が本質**。`p=2` では偽(p-stability の反例 `S₄`, `p=2`)。証明のどこかで `p≠2` が
  効く(典型的には SL(2,p) の構造 / `-1 ≠ 1` / `2` が可逆)。`p=2` を最後まで通さないこと。
- 二次 `(x−1)²=0` ⇒ Jordan ブロックは全てサイズ `≤ 2`、`[V,x]=im(x−1) ⊆ ker(x−1)=C_V(x)`、
  `|V:C_V(x)| = p^{rank(x−1)}`、`rank ≤ dim/2`。

## repo で使える部品(確認済・sorry-free)

| 部品 | 名前 / 場所 | 用途 |
|---|---|---|
| **BG Thm 2.6** (体一般, 2-dim faithful) | `OddOrder.BG.Ch1.S02.odd_two_dim_sylow_abelian` / `odd_two_dim_abelian`([S02_Representations.lean](../OddOrder/BG/Ch1_Preliminary/S02_Representations.lean) L4627/L4680) | **A.1 の主部品**。`Odd |G|`, `finrank F V = 2`, faithful `ρ`, `p ∣ |G|`, `CharP F p` ⇒ Sylow-`p` abelian ∧ `G' ≤ P` |
| p-group fixed vector | `OddOrder.GroupTheory.RepresentationTheory.PGroupFixedVector.{exists_fixed_vector_ne_zero, invariants_ne_bot}` (L289/L197) | **A.1 と Case `q=p`**: char-`p` で `p`-群の固定ベクトル `≠ 0` |
| 巡回作用の固有空間 | `OddOrder.RepresentationTheory.EigenspaceUnderCyclicAction.*`([…/EigenspaceUnderCyclicAction.lean](../OddOrder/GroupTheory/RepresentationTheory/EigenspaceUnderCyclicAction.lean), 918 行) | BG Prop 2.4。固有空間分解の道具。**部分的に流用可かも**(char-0 寄りだが eigenspace tooling) |
| mathlib | `Representation` / `FDRep` / `Module.End` / `Module.End.eigenspace` / `Matrix.GeneralLinearGroup` / `Module.IsSimpleModule` / Maschke (char ∤ \|G\| で半単純) | 基盤 |

### A.1 の組み立てレシピ(prover への確認用、follow-on)

A.1: `V` 2-dim over `F` (odd char `p`), `G ≤ GL(V)` 有限既約, `|G|` 奇 ⇒ `p ∤ |G|`。
1. `p ∣ |G|` と仮定。
2. `odd_two_dim_sylow_abelian` ⇒ Sylow-`p` `P` は abelian, `G' ≤ P`。
3. `G' ≤ P` ⇒ `P ⊴ G`(`P/G'` は abelian `G/G'` の部分群なので正規)。
4. `P` は正規 `p`-群 → char `p` 作用で `C_V(P) ≠ 0`(`PGroupFixedVector`)、`C_V(P)` は
   `G`-不変 → 既約より `C_V(P) = V` → `P` は自明作用 → 忠実より `P = 1`。`p ∣ |G|` と Sylow に矛盾。
5. ∴ `p ∤ |G|`。∎

## 直接は使えないもの(誤解しやすい点)

- `gl2_pSubgroup_centralizes_of_normalizes` (Lem 7.3, [S7A1](../OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean) L1269) と
  `sylow_normal_of_elementary_normal_P_theorem` (Thm 7.5, [S7A2](../OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean) L1216):
  **本 issue には使わない**(reduced J(P) 経路の道具。理由はノート §0)。
- `Clifford.lean`(`OddOrder.RepresentationTheory`)は **ℂ 上の指標 Clifford**(Isaacs 6.5、
  しかも証明 deferred)。本 issue が要るのは **`F̄_p` 上の加群 Clifford**(homogeneous component
  分解)で別物。流用不可。

## 作る必要があるインフラ(char-`p` 加群表現論)

縮約証明の中で要りそうなもの(過不足は実装で判明):
- **加群の primitivity / imprimitivity**(induced module、系 of imprimitivity blocks)。
  mathlib に直接は無い見込み → 必要分を `OddOrder/GroupTheory/RepresentationTheory/` に新規。
- **加群 Clifford**: 正規部分群への制限の homogeneous 分解、alg-closed 上で normal abelian は
  scalar に作用(primitive のとき)。
- **二次元 (transvection / Jordan サイズ ≤2) の固有値・Jordan 解析**。

`OddOrder/GroupTheory/RepresentationTheory/AbsolutelyIrreducible.lean` は現状 40 行 skeleton。
ここを膨らませる手もある。

## 証明戦略の出発点(⚠️ 要検証 — 下記「原典が無い」注意)

Gorenstein 3.8.1 の標準的な縮約は概ね次の形(**FF-module / quadratic pair 理論の特殊例**):
1. **WLOG `G` は `V` 上 primitive**。imprimitive なら `V = V₁ ⊕ … ⊕ V_k` (`k>1`) を `G` が
   推移置換。二次元 `x` のブロック置換への作用 + 二次条件 + 既約性で primitive に帰着。
2. **primitive + alg-closed** ⇒ normal abelian subgroup は scalar 作用(Clifford + primitivity)。
   ⇒ `F(G)`/socle の構造が強く制約される。
3. **二次元の固有値/Jordan 構造 + 制約された正規構造 + 2 生成** ⇒ `dim V = 2`。

これはあくまで orientation。**正確な step は実装者が確定すること**(記憶ベースで未検証)。

## ⚠️ 重要: Gorenstein 原典は references/ に無い

本プロジェクトの `references/` には Isaacs FGT / BG / Peterfalvi しか無く、**Gorenstein 1968
"Finite Groups" §3.8 (p.105) は読めない**。よって本 issue は「既知の証明を翻訳する」のではなく
**証明を再構成 or アクセス可能な別ソースから持ってくる**作業を含む。

- 最初の sub-task は「2 生成・二次・既約 ⇒ dim 2」の **証明の確定**(=調査)にしてよい。
- この内容(quadratic action / FF-module / quadratic pairs)が書かれている標準文献:
  Kurzweil–Stellmacher _The Theory of Finite Groups_ (quadratic action の章), Aschbacher
  _Finite Group Theory_, Gorenstein–Lyons–Solomon。**プロジェクトに無いので、必要なら
  ユーザーに該当ページの供与を依頼**(BG 同様 references/ に追加してもらう)のが確実。
- BG Thm A.1/A.2 の原文は [`references/bg/local-analysis.mmd`](../references/bg/local-analysis.mmd) L4460–4472。

## やること(着手順)

- [ ] **(調査)** 「2 生成・二次・既約 (`p` 奇, `F̄_p`) ⇒ dim V = 2」の証明を確定。原典不在のため
      再構成 or ソース供与依頼。`p=2` 反例で `p≠2` の使いどころを特定。
- [ ] **(A.1)** 上記レシピで A.1 を組む(部品済、interface/型の早い確認)。新規ファイル
      `OddOrder/BG/AppA_PStability.lean`(または相当)を作る。配置は ROADMAP / 既存 BG 構成に合わせる。
- [ ] **(インフラ)** 縮約に要る char-`p` 加群表現論(primitivity / 加群 Clifford / 二次解析)を
      `OddOrder/GroupTheory/RepresentationTheory/` に必要分だけ新規実装。
- [ ] **(縮約)** `quadratic_two_generated_irreducible_finrank_eq_two` を証明。
- [ ] **(A.2)** 縮約 + A.1 で A.2(`|G|` 偶)を閉じる。

## 完了条件

- 次元縮約補題(`finrank F V = 2`)が `sorry`/`axiom` 無しで証明され `lake build` が通る。
- できれば A.1・A.2 も sorry-free で配線(A.2 = 本ルートの真のゲート)。
- docstring に `**BG Thm A.2** (Gorenstein 3.8.1 次元縮約パート)` のトレーサビリティ。
- 新規インフラは `OddOrder/GroupTheory/RepresentationTheory/` 配下、mathlib 互換命名。
- 完了後 `notes/meta/bg_s6_appAB_route_2026_05_28.md` §0 と per-section
  [`notes/bg/appA_pstability.md`](../notes/bg/appA_pstability.md) の状態を更新。

## 参照

- **設計・依存閉包・リスクモデル(必読)**: [`notes/meta/bg_s6_appAB_route_2026_05_28.md`](../notes/meta/bg_s6_appAB_route_2026_05_28.md) **§0**(spike 訂正)
- per-section: [`notes/bg/appA_pstability.md`](../notes/bg/appA_pstability.md) / [`notes/bg/s06_additional.md`](../notes/bg/s06_additional.md)
- BG 原文: `references/bg/local-analysis.mmd` — A.1 L4460–4464, **A.2 L4468–4472**, A.3 L4476, A.4 L4480–4485, A.5 L4488–4513, App.A 序文 L4452–4458
- repo 部品: S02 `odd_two_dim_sylow_abelian` (L4680) / `PGroupFixedVector` / `EigenspaceUnderCyclicAction`
- 隣接 issue: #28 (Prop 2.4 eigenspace), #33 (AbsolutelyIrreducible), #35 (OddTwoDimRepr — Thm 2.6 は実際は S02 に実装済なので #35 は陳腐化。要整理)
- 下流(A.2 が出来た後): A.3 → A.4(a/b/c) → A.5 → App.B(B.1–B.4)→ BG §8–§16 を L(S) 化
