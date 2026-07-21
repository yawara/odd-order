---
id: 3024
slug: gorenstein-ch8s2-glauberman-zj
title: "Gorenstein Ch.8 §2 (Glauberman ZJ) の移植 — BG Thm 6.2 literal J(S) 一般形の唯一の障害"
created: 2026-07-19
---

# Gorenstein Ch.8 §2 (Glauberman ZJ) の移植 — BG Thm 6.2 literal J(S) 一般形の唯一の障害

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景 — なぜ必要か

issue 3017 (BG Thm 6.2 の literal `J(S)` 一般形) の調査 (2026-07-19) で、**唯一の障害がこれ**
だと確定した。3017 は本 issue に blocked。

BG Thm 6.2: `G` odd solvable, `p` 素数, `S ∈ Syl_p(G)` ⟹ `Z(J(S))·O_{p'}(G) ⊴ G`。
**BG p.49 は証明を書いていない** — 本文は "Proof. **G**, Theorem 6.5.1, p. 234 and
Theorem 8.2.11, p. 279. □" という Gorenstein への引用のみ (`.mmd` は該当ページを落としている
ので PDF で確認)。**G** 8.2.11 が Glauberman ZJ。

⟹ CLAUDE.md が Gorenstein 参照を認める**まさに名指しのケース**:
「Isaacs が欠く場合 (典型: ZJ / p-stability 周り = **G** Ch.3 §8 / Ch.6 §5 / Ch.8 §2) のみ
Gorenstein を参照」。Gorenstein 本体を独立に形式化するのではなく、**BG が省略した証明本体を
埋める**ためのもので、in-scope。

## 何が要るか

`S06_Thm62JS.lean:69` の `zCenterThompsonJ_sup_oPiCore_normal_of_reduced` は仮説 `hZJ` を
未充足で持っており、それを埋めれば 3017 は即閉じる。必要な形:

```lean
theorem zCenterThompsonJ_normal_of_pStable_pConstrained [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hstable : IsPStable p G)          -- or Odd (Nat.card G), via thmA4
    (hOp' : oPiCore {q | q ≠ p} G = ⊥)
    (hconstr : centralizer (opCore p G : Set G) ≤ opCore p G)   -- 既存: S7B1_NormalJ.lean:68
    (S : Sylow p G) :
    (centralizer (thompsonJ (S : Subgroup G) p : Set G) ⊓ thompsonJ (S : Subgroup G) p).Normal
```

⚠ **仮説 2 つは既に repo に在る** — `BG.AppA.IsPStable` (`AppA_PStability.lean:127`、
`thmA3/thmA4a/thmA4b/thmA4c/thmA5_part1/thmA5_part2` つき) と p-constraint
(`Isaacs.Ch07.centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot`)。**欠けているのは ZJ 定理本体**。

Gorenstein Ch.8 §2 (pp. 270-279, `references/gorenstein/finite-groups.mmd` L5431-5622) の鎖を
まるごと要する: Lem 2.1 (`A = C_P(A)`) / 2.2 / 2.3 / **Thm 2.4 (Thompson)** /
**Thm 2.5 (Thompson Replacement)** / 2.6 / **Thm 2.7 (Glauberman Replacement)** /
**Lem 2.8** (`[B,A;i]` と下降中心列) / 2.9 / **2.10** (`B ⊓ Z(J(P)) ⊴ G`) / 2.11。
repo に**一つも無い** (`grep "replacement"` は Isaacs 3.31 Hartley–Turull しか当たらず無関係)。

## ⚠ 最大のリスク = `J(P)` の定義違い (着手前に設計判断が要る)

- **Gorenstein/BG の `J(P)`** = **abelian** 部分群のうち**最大位数**のもので生成。
- **本 repo の `Subgroup.thompsonJ`** (`OddOrder/GroupTheory/ThompsonSubgroup.lean:64-72`)
  = Isaacs 版で、**elementary** abelian 部分群のうち最大位数のもので生成
  (`maxElemAbelianIn` が `IsElementaryAbelian p` を要求 — 2026-07-19 に定義を実読して確認)。

Gorenstein §2 の機構は **Lemma 2.1 (`A ∈ A(P) ⟹ A = C_P(A)`)** に乗っており、これは
**elementary 版では偽**。Gorenstein 自身も変種問題に言及 (mmd L5470)。

⟹ faithful な移植には **第二の Thompson 部分群 `J_a` (abelian 版) + その API** を新設するか、
elementary 版向けに議論を非自明に adapt するかの**設計判断**が要る。着手時はここを最初に決めること。

## 規模見積

**Lean 2,000-4,000 行 / 複数 session** (Isaacs Thm 7.6 が同程度の教科書議論で
`S7B1`+`S7B2` 約 3,500 行、という実測に照らした較正)。上の `J_a` 新設分は別途。

## 位置づけ

- **恒久対象外ではない** (CLAUDE.md: 文献引用のみで本文に証明が無い結果も低優先繰延であって
  恒久除外しない)。BG の numbered result であり、in-scope。
- ただし **FT にも他の下流にも gate は無い**: `L(S)` 一般形 (book 推奨代替) が済んでおり、
  FT が使う `J(S)` 形は reduced case か `L(S)` で満たされている。math-comp も ZJ を形式化せず
  `L(S)` で通している。⟹ **優先度は低い**が、やる価値のある genuine な穴。

## 参照

- issue 3017 (本 issue に blocked)。
- BG p.49 (PDF; `.mmd` は落としている) — Thm 6.2 の "Proof. **G** 6.5.1 / 8.2.11" 引用。
- BG mmd L4593 — 「odd order に絞れば `J(S)` の代わりに別の特性部分群でより短い証明になる」。
- `coq/theories/BGappendixAB.v:16` / `BGsection1.v:35` — math-comp が ZJ を Puig `L(S)` で代替。
- `references/gorenstein/finite-groups.mmd` L5431-5622 (Ch.8 §2)。

## ✅ 2026-07-21 (lane c): 設計判断確定 — abelian 版 `J_a` 新設 (claim = issue 9403)

「⚠ 最大のリスク」の設計判断を決着:

- **BG の J(S) = Gorenstein 版** (abelian・最大位数) と確定 — BG は J を自前定義せず
  (記号表 L8611 の初出 = Thm 6.2 自身、証明 = G 引用のみ)。
- **elementary 版への adapt は不可能**: G Lem 2.1 (`A = C_P(A)`) の証明は
  「`x ∈ C_P(A)` ⟹ `⟨A,x⟩` abelian でより大」で、全 abelian 中の最大性が本質。
  elementary 版では `⟨A,x⟩` が elementary と限らず**偽**。
- ⟹ **`Subgroup.thompsonJAbelian` を新設して忠実移植** (`OddOrder/GroupTheory/
  ThompsonSubgroupAbelian.lean`、shared infra claim = **issue 9403** 承認待ちでなく
  claim-before-build 手順済)。
- ⚠ **副産物**: `S06_Thm62JS.lean:71` の `hZJ` が elementary `thompsonJ` で符号化されて
  いるのは BG literal との**ミスマッチ**。J_a 完成後に hZJ・結論とも J_a 形へ言い直す
  (reduction 証明は共変性 lemma を J_a 版へ差し替えて再利用)。3017 close の一部。

## 付随 — lane a への申し送り (Isaacs/Ch07 は lane a territory ゆえ本 lane で直さない)

調査中に stale docstring 3 件を検出:
- `S7B2_NormalJ_PComplement.lean:1421-1424` (`normal_J`) — 「Remaining local axioms:
  `step4_5_normal_J_hypotheses` … `step8_normal_J_closure`」は**すべて誤り**。前者は
  `private theorem` (:864)、`step8_normal_J_closure` は**存在しない**。`normal_J` は
  AxiomsCheck:1548 で axiom-clean 宣言済、Ch07 は sorry-free。
- `S7B2_NormalJ_PComplement.lean:1300-1307` — 同じ「Step 4-5 axiom」「Step 8 axiom」表現。
- `S7B1_NormalJ.lean:1616-1621` + header :22-37 — 「Step 7 の結論を axiomatize する」は stale
  (`omega1ZCenterOpCore_relIndex_inter_A_le` として landed、tracking issue 0036 も closed)。
