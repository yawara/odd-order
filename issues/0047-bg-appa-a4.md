---
id: 47
slug: bg-appa-a4
title: "BG App.A Thm A.4(a/b/c) — p-stable / Hall-Higman 6.1 / stability lift"
created: 2026-05-29
---

# BG App.A Thm A.4(a/b/c) — p-stable / Hall-Higman 6.1 / stability lift

## 背景

issue [#0043](closed/0043-bg-appa-a3-pstability.md) で **A.3** (`thmA3`) を sorry-free
完成。App.A 連鎖の次ゲートが **A.4(a/b/c)**:

```
Thm 6.2 ⟸ App.B B.4 ⟸ A.5 ⟸ A.4(c) [本 issue] ⟸ A.3 ✅ ⟸ A.2 ✅ ⟸ A.1 ✅
Thm 6.1 = A.4(b) [本 issue]  (§7/§8 が独立に引用)
```

BG mmd L4478: 「We now move to Section 6.5 of **G**. By using Theorem A.3 instead of
Theorem 3.8.4(e), we obtain special cases of Theorems 6.5.1-6.5.3」。つまり A.4 =
**Gorenstein 6.5.1-6.5.3 を A.3 で置換した翻訳**。経路は
[`notes/meta/bg_s6_appAB_route_2026_05_28.md`](../notes/meta/bg_s6_appAB_route_2026_05_28.md)、
per-section は [`notes/bg/appA_pstability.md`](../notes/bg/appA_pstability.md)。

## Statement (BG mmd L4480)

`p` 奇素数, `G` solvable odd order, `P` を `G` の `p`-部分群とする:

- **(a)** `O_p(G) = 1` ⇒ `G` は `p`-stable.
- **(b)** `P` が Sylow `p` ⇒ `P` の全 normal abelian 部分群は `O_{p',p}(G)` に含まれる
  (= **Thm 6.1** = Hall-Higman 特殊形).
- **(c)** `O_{p'}(G)·P ◁ G` かつ `A` が `N_G(P)` の `p`-部分群で `[P,A,A]=1` ⇒
  `A·C_G(P)/C_G(P) ⊆ O_p(N_G(P)/C_G(P))`.

A.5 は (c) を消費 (`[P,A,A] ⊆ [A,A] = 1` より各 abelian `A` に適用)。

## パート別分析

### (a) — ✅ 即実装可能: thmA3 の対偶

`thmA3`: `[Finite G] (p≠2) (O_p(G)=⊥) (¬IsPStable) ⇒ ¬Odd(card G)`。
対偶 (奇数位数で): `(p≠2) (Odd) (O_p(G)=⊥) ⇒ IsPStable`。
→ `by_contra h_not; exact thmA3 hp_odd hOp h_not hodd`。**~5 行、solvable 不要**。

```lean
theorem thmA4a [Finite G] (hp_odd : p ≠ 2) (hodd : Odd (Nat.card G))
    (h_Op_trivial : OddOrder.Isaacs.Ch01.opCore p G = ⊥) :
    IsPStable p G := by
  by_contra h_not
  exact thmA3 hp_odd h_Op_trivial h_not hodd
```

### (b) — deep: = Thm 6.1 = Hall-Higman 特殊形 (Gorenstein 6.5.2 翻訳)

`P ∈ Syl_p(G)`, `G` solvable odd ⇒ 全 normal abelian `A ◁ P` が `O_{p',p}(G)` に含まれる。
§7/§8 本文が独立に引用 (J→L 置換と直交、route note §4)。
証明本体 = Gorenstein 6.5.2 を A.3 で置換した翻訳。**未調査** (Gorenstein Ch.6 §5 読解要)。

### (c) — critical path: stability lift (Gorenstein 6.5.3 翻訳)

`O_{p'}(G)·P ◁ G`, `A ≤ N_G(P)` `p`-subgroup, `[P,A,A]=1` ⇒ `AC_G(P)/C_G(P) ⊆ O_p(N_G(P)/C_G(P))`。
A.5 → B.4 → Thm 6.2 の本線。証明本体 = Gorenstein 6.5.3 を A.3 で置換。**未調査**。

## やること (粒度別)

- [ ] **(a) `thmA4a`** — thmA3 の対偶 (sorry-free, ~5 行). 即着手。
- [ ] **(b)/(c) 投資調査**: Gorenstein Ch.6 §5 (`references/gorenstein/finite-groups.mmd`,
  Thm 6.5.1-6.5.3) を読み、A.3 (= thmA3) で 3.8.4(e) を置換する具体ルートを per-part で記述。
- [ ] **(c) `thmA4c`** (critical path: A.5/B.4 が要する) を先に。必要 API: `O_{p',p}` =
  `oPiPCore` (repo), `O_{p'}` = `oPiCore`, `N_G(P)/C_G(P)` 商, `[P,A,A]` lower central。
- [ ] **(b) `thmA4b`** (= Thm 6.1): normal abelian ≤ `O_{p',p}`. §6 reduced-case
  (`S06_Additional`) との関係を確認 (一般形は未実装)。
- [ ] notes/bg/appA_pstability.md の A.4 節を更新。

## 完了条件

- `thmA4a` / `thmA4b` / `thmA4c` を `OddOrder/BG/AppA_PStability.lean` に sorry-free 追加。
- `lake build OddOrder` green、axiom-clean。
- docstring に `**BG Thm A.4(x)** (= Gorenstein 6.5.y 翻訳, mmd L4480)` トレーサビリティ。
- 後続 A.5 (`thmA5`) が (c) を使って組める状態。

## 参照

- BG mmd L4480 (A.4 statement), L4488-4516 (A.5 statement + proof, A.4(c) を使用)
- Gorenstein mmd: Ch.6 §5 Thm 6.5.1-6.5.3 (proof 本体の供給元)
- repo: `OddOrder.BG.AppA.thmA3` / `IsPStable` ([AppA_PStability.lean](../OddOrder/BG/AppA_PStability.lean))
- repo: `OddOrder.Isaacs.Ch01.opCore` (`O_p`), `oPiCore` (`O_{p'}`), `oPiPCore` (`O_{p',p}`) — 要確認
- closed [#0043](closed/0043-bg-appa-a3-pstability.md) (A.3)
- notes: [`bg_s6_appAB_route_2026_05_28.md`](../notes/meta/bg_s6_appAB_route_2026_05_28.md) §3 (真のゲート = A.4(b)+A.4(c)),
  [`appA_pstability.md`](../notes/bg/appA_pstability.md)
