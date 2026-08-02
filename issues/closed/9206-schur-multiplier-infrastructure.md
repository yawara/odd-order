---
id: 9206
slug: schur-multiplier-infrastructure
title: "Schur 乗数 M(G) の形式化 (Isaacs 5A.5-5A.8 の前提、shared infra claim)"
created: 2026-07-26
---

# Schur 乗数 `M(G)` の形式化 (shared infra claim, lane a)

## claim

**lane a が claim** (issue 1055 = Isaacs 演習問題 campaign の §5A で必要になった)。
着手前に検索して既存が無いことを実測済 (下記)。

## 実測した現状 (2026-07-26)

- **mathlib に無い**: `SchurMultiplier` / `schurMultiplier` は mathlib に存在しない
  (`grep -rl` で 0 件)。`Mathlib/GroupTheory/SchurZassenhaus.lean` は別物 (Schur-Zassenhaus)。
- **repo にも無い**: `OddOrder/Isaacs/Ch05_Transfer/CentralTransfer.lean` の module docstring が
  「Schur multiplier 概念 (M(G), 中心 extension の universal) 自体は mathlib 未収載で
  full 形 (Sylow_p(Γ/Z) noncyclic) は別途」と明記している。Thm 5.4 は**弱形**
  (`not_isMulCommutative_sylow_of_le_commutator_inf_center`: `Z ≤ Γ' ⊓ Z(Γ)`, `p ∣ |Z|` ⇒
  Sylow_p(Γ) 非可換) しか持っていない。
- ⚠ **紛らわしい同名**: `OddOrder/Isaacs/Ch04_Commutators/Mann.lean` の `mannSubgroup G` も
  Isaacs では `M(G)` と書かれるが、これは **Mann の部分群** (小さい共役類で生成) であって
  Schur 乗数ではない。4B.5 の `M(G)` はこちら。**混同しないこと**。

## これが前提になっている演習

- **Isaacs 5A.5**: `C ⊴ G` 巡回で `G/C` 巡回 ⟹ `|M(G)| ∣ |C : G'|`
- **Isaacs 5A.6**: 位数 `2n` (`n > 2`) の二面体群で `|M(D)| = 2`
- **Isaacs 5A.7**: `B`, `C` 巡回で `BC = G`, `B ⊓ C > 1`, `C ⊴ G`, `|C : G'| = n`
  ⟹ `|M(G)| < n` (系: semidihedral / 一般四元数群の Schur 乗数は自明)
- **Isaacs 5A.8**: `|M(A × B)| ≥ |M(A)||M(B)|`、`(|A|,|B|) = 1` なら `M(A × B) = M(A) × M(B)`

Isaacs Ch.5 の本文 (Thm 5.4 の full 形) も同じ前提を要求する。

## 設計の方針 (未着手、要検討)

Isaacs の定義は「中心拡大 `Γ` で `Z ≤ Γ' ⊓ Z(Γ)` となる `Z` の**最大**のもの」
(universal central extension の核)。Lean での候補:

1. **Schur 表現群 (representation group) 経由**: `Γ` を `G` の中心拡大で `Z ≤ Γ' ⊓ Z(Γ)`,
   `|Z|` 最大となるものとして構成し、`M(G) := Z`。存在と一意性 (同型を除く) が要る。
2. **`H₂(G, ℤ)` 経由**: mathlib の群コホモロジー (`Mathlib/RepresentationTheory/GroupCohomology`)
   を使う。`M(G) ≅ H₂(G, ℤ)` (自明係数)。mathlib の群コホモロジーの成熟度を実測してから決める。
3. **Hopf の公式**: `G = F/R` (自由表示) で `M(G) ≅ (R ⊓ [F,F]) / [F,R]`。
   自由群と表示の扱いが要る。

⚠ 1 は Isaacs の流儀に最も近く 5A.5-5A.8 の証明もそのまま写せるが、存在証明が重い。
2/3 は定義が軽い代わりに Isaacs の議論との橋渡しが要る。**着手時に 3 案を実測比較すること**。

## 3 案の実測 (2026-07-26)

| 案 | mathlib の現状 | 評価 |
|---|---|---|
| 1. Schur 表現群 (中心拡大の universal) | 中心拡大そのものは `GroupExtension` があり repo にも `GroupTheory/CentralElementaryExtension.lean` 等の資産あり。**universal / 表現群の存在は無い** | Isaacs の議論に最も近いが**存在証明が重い** |
| 2. `H₂(G, ℤ)` | `Mathlib/RepresentationTheory/Homological/GroupHomology/LowDegree.lean` に **`abbrev H2 := groupHomology A 2`** が実在 (`GroupCohomology` 側にも `H2`)。ただし **`H₂` と中心拡大を結ぶ補題は mathlib に無い** (`grep central extension` は 0 件) | 定義は軽いが Isaacs の議論との橋渡しを自作することになる |
| 3. Hopf の公式 | `FreeGroup` / `PresentedGroup` はあるが Hopf 公式は無い | 同上 + 表示の扱いが重い |

## ⭐ 採用方針 (2026-07-26 に決定): **まず `M(G)` を定義せずに書けるところまで書く**

5A.5-5A.8 の内容を見ると, **上界の主張はすべて「任意の中心拡大について」の ∀-形で述べられる**:

- **5A.5** `|M(G)| ∣ |C : G'|` ⟹ 「`Γ` が `G` の中心拡大で `Z ≤ Γ' ⊓ Z(Γ)` なら `|Z| ∣ |C : G'|`」
- **5A.7** `|M(G)| < n` ⟹ 同様の ∀-形
- **5A.6 / 5A.8** の上界側も ∀-形

これらは **`M(G)` の定義 (universal object の存在) をまったく必要としない**。repo の
Isaacs Thm 5.4 弱形 (`not_isMulCommutative_sylow_of_le_commutator_inf_center`) が
すでに同じ流儀を採っている。

`M(G)` の定義が本当に要るのは **∃-側** (5A.6 の `|M(D)| = 2` の下界, 5A.8(a) の
`≥ |M(A)||M(B)|`) だけで, そこは**具体的な中心拡大を構成**すれば足りる (universal 性は不要)。

⟹ **手順**: (i) 「中心拡大 + `Z ≤ Γ' ⊓ Z(Γ)`」を述語として切り出す →
(ii) 5A.5 / 5A.7 と 5A.6 / 5A.8 の上界を ∀-形で証明 →
(iii) ∃-側は具体構成 → (iv) それでも universal object が要ると判明した場合にのみ案 1/2 に進む。

## 状態

- [x] 3 案の実測比較 (2026-07-26)
- [x] 採用方針の決定 (∀-形で `M(G)` 定義を回避)
- [x] 中心拡大述語の切り出し = `IsStemExtension f` (全射 `f : Γ →* G` + `ker f ≤ Γ' ⊓ Z(Γ)`)
      — 同型 `Γ/Z ≅ G` を運ぶより核で表す方が comap 計算が全部効いて圧倒的に軽い
      (`Subgroup.relIndex_comap` / `comap_map_eq` / `map_comap_eq_self_of_surjective` で
      `|C : G'| = |f⁻¹C : Γ'|` が 3 行)
- [x] **5A.5** `card_ker_dvd_relIndex_commutator` (2026-07-26)
- [x] **5A.7** `card_ker_lt_relIndex_commutator` (2026-07-26)
- [x] **5A.6** (2026-07-26) — 上界 `card_ker_dvd_two_of_dihedral` + 下界
      `isStemExtension_dihedralReduce` (`ProblemsDihedralMultiplier.lean`)。
      ⚠ 書籍は `2^n` (二面体 2-群) であって `2n` ではない (`pdftotext` の上付き潰れ;
      `2n` 版は n 奇数で偽)。実装は**偶数一般形**でより強い。
      下界の witness = reduction hom `D_{4t} ↠ D_{2t}` — **∃-側は universal object を
      要さず具体構成 1 本で足りる**ことの実例
- [x] **5A.8(a)** `isStemExtension_prodMap` / `card_ker_prodMap`
      (`ProblemsSchurMultiplier.lean`) — ∃-側は具体構成 `f.prodMap g` 1 本
- [x] **5A.8(b)** `card_ker_eq_mul_card_ker_stem` (`ProblemsProductMultiplier.lean`)
      — coprime 直積を中心積に分解して `|ker h| = |ker f_A|·|ker f_B|`
- [x] **Isaacs Cor 5.4 の full 形** = `not_isCyclic_sylow_quotient_of_le_commutator_inf_center`
      (`CentralTransfer.lean`) — 「`Z ≤ Γ' ⊓ Z(Γ)`, `p ∣ |Z|` ⇒ Sylow_p(Γ/Z) 非巡回」で
      **書籍の結論そのもの**。universal object は不要だった
      (⚠ 書籍は Theorem でなく **Corollary** 5.4)。2026-08-03 実測で確認、
      同 leaf の「full 形は別途」という stale 注記も同時に訂正。

## ✅ close (2026-08-03)

上の全項目が landing 済であることを実測で確認したので close する。
`M(G)` の universal object は**結局どの演習にも不要**だった — Isaacs 5A.5–5A.8 は
すべて `IsStemExtension` の ∀-形 (上界) と具体構成 (∃-形/下界) の対で書けている。

## 実装メモ (2026-07-26)

`OddOrder/Isaacs/Ch05_Transfer/ProblemsSchurMultiplier.lean`。

- `IsStemExtension` を「部分群 `Z` + 同型 `Γ/Z ≅ G`」でなく「全射 `f` + `ker f`」で持つのが鍵。
  quotient-of-quotient (Noether III) の transport が丸ごと不要になる。
- `A := f⁻¹(C)` の可換性は mathlib
  `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` を制限 hom
  `(f.comp A.subtype).codRestrict C _ : ↥A →* ↥C` に適用するのが最短
  (生成元を取って `a = γ^k z` と書く手作業は不要)。
- `Γ/f⁻¹(C) ≅ G/C` は `QuotientGroup.quotientKerEquivOfSurjective ((mk' C).comp f)` +
  `quotientMulEquivOfEq`。
- ⚠ `Subgroup.relIndex_comap` の第 1 明示引数は `H` (comap される側) — `f` を先に渡すと
  `Subgroup ?m` と型が合わずエラー。正しくは `Subgroup.relIndex_comap H f K`。
- ⚠ `push_neg` は deprecated 警告 (`--strict` 赤) — `Nat.le_of_not_lt` を直接使う。
