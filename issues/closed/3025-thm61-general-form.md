---
id: 3025
slug: thm61-general-form
title: "BG Thm 6.1 一般形: O_{p',p}(G) は S の任意の abelian normal 部分群を含む (thmA5_part2 経由)"
created: 2026-07-19
---

# BG Thm 6.1 一般形: O_{p',p}(G) は S の任意の abelian normal 部分群を含む (thmA5_part2 経由)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

issue 3017 (BG Thm 6.2 の literal `J(S)` 一般形) の調査 (2026-07-19) 中に発見した、
**隣接する tractable な特殊化債務**。3017/3024 とは違い **Glauberman ZJ に blocked されない**。

**BG Thm 6.1**: `O_{p',p}(G)` は `S ∈ Syl_p(G)` の任意の abelian normal 部分群を含む。

現状:
- 一般形は**未**。repo にあるのは reduced な `J(P)`-instance =
  `BG.Ch1.S06.thompsonJ_le_oPiPrimePiCore_of_odd` (`S06_Additional.lean:152`) で、
  `C_G(Z(P)) = P` に gated。
- `notes/bg/s06_additional.md` の残課題 3 に一般形が挙がっている。
- ⚠ なお BG Thm 6.1 自体は `AppA_PStability.lean` の `thmA4b` として在る (book が Thm 6.1 =
  Thm A.4(b) と同一視しているため; survey L476)。**本 issue が求めるのは「`O_{p',p}(G)` が
  `S` の abelian normal 部分群を含む」という形の一般形**で、これが reduced instance しか
  無い、という債務。着手時にまず両者の関係を実測で確認すること。

## 想定経路 (未検証、着手時に要確認)

既証明の **`thmA5_part2`** (`AppA_PStability.lean:1501`) が使えそう:
`Ḡ = G/O_{p'}(G)` で `P := O_p(Ḡ)` と取ると、
- `thmA5_part2` の仮説 `hCP` (`C_G(P) ⊓ O_p(G) ≤ P`) は `… ⊓ P ≤ P` に退化して自明に真、
- 仮説 `hX` は、`A ⊴ S̄` abelian なら `O_p(Ḡ) ≤ S̄` に正規化されるので満たされる。

`O_{p'}` reduction 自体は repo 内に既に 2 回 mirror されている
(`AppB_Thm62.zCenter_lOdd_sup_oPiCore_normal` と `S06` 側)。

⚠ 上記は調査 subagent の見立てであって**未検証**。着手時に `thmA5_part2` の実署名を読み、
仮説の退化が本当に起きるかを確かめること (本 session は stale label / 名前一致の罠を
3 回踏みかけている)。

## 参照

- issue 3017 (pending, ZJ に blocked) / issue 3024 (Gorenstein Ch.8 §2)。
- `notes/bg/s06_additional.md` 残課題 3。
- survey `notes/meta/three_books_full_survey_2026_07_16.md` L476 (BG §6 概況)。

---

## 判定 (2026-07-19): **一般形は既に存在していた** — 本 issue は close

Step-0 の premise 検証 (着手前に必須と指示) で、**本 issue の前提が誤りだった**ことが判明した。

### 1. BG Thm 6.1 の一般形は `AppA.thmA4b` として既に済

`OddOrder/BG/AppA_PStability.lean:1387`:

```lean
theorem thmA4b [Finite G] (hp_odd : p ≠ 2) (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    (P : Sylow p G) {A : Subgroup G} (hA_le : A ≤ (P : Subgroup G))
    (hA_norm : (P : Subgroup G) ≤ Subgroup.normalizer (A : Set G)) [IsMulCommutative A] :
    A ≤ OddOrder.Isaacs.Ch03.oPiPrimePiCore ({p} : Set ℕ) G
```

これが目標そのもの (`A` abelian、`hA_le` + `hA_norm` で `A ⊴ S`、結論 `A ≤ O_{p',p}(G)`)。
**`O_{p'}(G) = ⊥` も `C_G(Z(P)) = P` も仮定していない** — `O_{p'}` reduction は証明内部
(Steps 1-7: `N = O_{p'}(G)` で商、`R̄ := O_p(Ḡ)`、`stabilityLiftAux`、Hall-Higman) で行われる。
AxiomsCheck:2490 で axiom-clean 登録済、commit `9954fcc5c` で landed。

BG 自身が mmd L4627 で「Note that Theorem A.4(b) is just Theorem 6.1」と同一視している
(定理文そのものは mmd L1986)。

### 2. 想定していた `thmA5_part2` 経由は不要かつ誤り

`thmA5_part2` (`:1501`) は BG Thm A.5(2) で**別の主張** (`P`-normalized な abelian `p`-群で
生成される `X` について)。しかも `hOp' : O_{p'}(G) = ⊥` を `G` 自身に要求する。
本 issue が書いた「`hCP` が退化する」という見立ては、そもそも A.5(2) 経由の reduction が
不要なので moot だった。**着手前に premise を実測させた判断が正しかった。**

「gap がある」ように見えた原因は、§6 側に `thompsonJ_le_oPiPrimePiCore_of_odd`
(`S06_Additional.lean:165`) しか無く、これが `O_{p'}(G) = ⊥` + `C_G(Z(P)) = P` に gated な
真に弱い `J(P)` instance だったこと。

### 3. 実在した債務 = vacuous な `p ≠ 2` 仮説 (解消済)

`thmA4b` は `hp_odd : p ≠ 2` を持つが、book は「`p` is a prime」(任意)。奇数位数下では
`p = 2` は vacuous (Sylow 2-部分群が自明 ⟹ `A = ⊥`) なので、これは除去可能な特殊化債務
= CLAUDE.md が「docstring 注記で済ませず一般化せよ」と言うカテゴリ。

⟹ **`S06_Thm61.le_oPiPrimePiCore_of_abelian_normal_in_sylow`** (新 leaf
`OddOrder/BG/Ch1_Preliminary/S06_Thm61.lean:47`) として、`p ≠ 2` を外した §6 側の入口を追加。
`p = 2` 分岐は Sylow-2 自明性で処理、`p ≠ 2` 分岐は `thmA4b` を cite。sorry-free・axiom-clean
(AxiomsCheck 登録済)。**新規の数学は無し**。
新 leaf にしたのは `S06_Additional.lean` が 1655 行で 1500 行の分割 trigger を超えているため。

### 4. 本 issue 自身の誤り (記録)

- `AppA_PStability.lean` の所在は `OddOrder/BG/` であって `OddOrder/BG/Ch1_Preliminary/` ではない。
- reduced instance は `S06_Additional.lean:165` であって `:152` ではない。

### 5. 併せて訂正した stale 記述

- `S06_Additional.lean:33` の表 (Thm 6.1「一般形 TODO」/ Thm 6.2「一般形 TODO」) → 実態へ。
- `S06_Additional.lean:164` docstring 「一般形は別途 (残課題 3)」→ `thmA4b` を指すよう訂正。
- `notes/bg/s06_additional.md` 残課題 3 (完了) / 残課題 4 (issue 3024 に blocked) / L23 の
  「Thm 6.1 も実質的な新規証明」(Thm 6.1 については誤り) を訂正。
