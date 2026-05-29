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

- [x] **(a) `thmA4a`** — thmA3 の対偶 (sorry-free). 2026-05-29 完了 (`AppA_PStability.lean`)。
- [ ] **(b)/(c) 投資調査**: Gorenstein Ch.6 §5 (`references/gorenstein/finite-groups.mmd`,
  Thm 6.5.1-6.5.3) を読み、A.3 (= thmA3) で 3.8.4(e) を置換する具体ルートを per-part で記述。
- [ ] **(c) `thmA4c`** (critical path: A.5/B.4 が要する) を先に。必要 API: `O_{p',p}` =
  `oPiPCore` (repo), `O_{p'}` = `oPiCore`, `N_G(P)/C_G(P)` 商, `[P,A,A]` lower central。
- [ ] **(b) `thmA4b`** (= Thm 6.1): normal abelian ≤ `O_{p',p}`. §6 reduced-case
  (`S06_Additional`) との関係を確認 (一般形は未実装)。
- [ ] notes/bg/appA_pstability.md の A.4 節を更新。

## 投資調査メモ (2026-05-29)

### repo API は (b) 向けに揃っている

- **`O_{p',p}(G)` = `opPpPrimeCore` が repo に既存**
  ([`Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean:257`](../OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean) で
  `L = O_{p',p}(G) (opPpPrimeCore)` として使用)。`O_p` = `opCore`, `O_{p'}` も Ch04 で使用例多数。
  → (b) 「normal abelian ≤ `O_{p',p}`」の主役 API は新規実装不要。

### Gorenstein 6.5.1-6.5.3 の所在 (⚠️ Nougat 再番号に注意)

- **Nougat 抽出 mmd は章番号を振り直している**: BG が引く Gorenstein「Section 6.5 /
  Thm 6.5.1-6.5.3」は、mmd では **「Chapter 8 §1 *p-constraint and p-stability*」
  (L5373 章見出し / L5383 節見出し / L5385+ 本体)** に対応。
- ⇒ **`grep "6.5.1"` 等では statement 本体が出ない** (Nougat が "Theorem 1.x" 等に
  再番号した可能性)。次回は **mmd L5383-5420 を直接 Read** して 6.5.1/6.5.2/6.5.3 を
  同定する (または `references/gorenstein/finite-groups.pdf` の原番号で確認)。
- L5385「Theorems 6.3.3 and 6.5.3 show that a strongly p-solvable group ... p-constrained」、
  L5410「In view of Theorem 3.8.4 and the remark following Theorem 6.5.3」、
  L5415「extension of Theorem 6.5.2」が proof 後の引用。6.5.3 = p-constraint 定理らしい。
- BG mmd L4478 が明示する翻訳ルール: **A.3 (= `thmA3`) で Gorenstein 3.8.4(e) を置換**して
  6.5.1-6.5.3 の特殊形 (= A.4) を得る。3.8.4(e) の使用箇所を 6.5.x proof 中で特定するのが鍵。

### スコープ感

- **(a)** ✅ 完了 (thmA3 対偶)。
- **(b)/(c)** は Gorenstein Ch.8§1 (= 6.5) の p-constraint 定理翻訳で **deep / 多段**。
  専用セッション or sub-agent 向き。(c) (critical path: A.5/B.4) を (b) より優先推奨。

## A.4(c) 作業計画 (2026-05-29 着手、Gorenstein 精読済)

### 同定: A.4(c) = Gorenstein「condition (B)」(逐語一致)

Gorenstein mmd L5391 (Ch.8 §1 = BG の §6.5 を参照する章) に **condition (B)** が逐語:
> Let `P` be a `p`-subgroup of `G` such that `O_{p'}(G)P ◁ G`. Then if `A` is a
> `p`-subgroup of `N_G(P)` with `[P,A,A]=1`, we have `AC_G(P)/C_G(P) ⊆ O_p(N_G(P)/C_G(P))`.

= **A.4(c) そのもの**。さらに mmd「Theorem 1.3」(= **A.4(b)**: P∈Syl_p, A abelian normal of P
⇒ A ⊆ O_{p',p}) の証明が condition (B) を呼ぶ ⇒ **(c) が (b) の土台。(c) 優先で正しい**。

### 証明ルート (BG L4478 の翻訳規則)

condition (B) は「**G が non-p-stable な section を involve しない**ら成立」(Gorenstein,
proof of 6.5.3 末尾)。奇数位数可解 G では **全 section が O_p=1 で p-stable**
(= A.4(a) = `thmA3` の対偶) ⇒ condition (B) 成立。BG は Gorenstein 3.8.4(e) を **A.3 で置換**。
- ⚠️ Gorenstein 6.5.1-6.5.3 の **statement+proof 本体は mmd L5383 より前** (Gorenstein Ch.6 §5)。
  L5383+ は Ch.8 で結果を**使う**側。次回 mmd で Gorenstein Ch.6 §5 を特定して 6.5.3 proof
  末尾の「sections p-stable ⇒ (B)」argument を読む (Nougat 再番号で `grep 6.5.x` 不可)。
- 別ルート候補: repo Ch.04 の coprime action / p-solvable 機構 + `thmA3` で直接組めるか要検討
  (Gorenstein 逐語翻訳より短い可能性)。repo §7B `normal_J` 証明の stability-lift 部品も再利用候補。

### Lean statement draft + 必要 API (確認済)

```lean
theorem thmA4c [Finite G] (hp_odd : p ≠ 2) (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    {P : Subgroup G} (hP : IsPGroup p P)
    (hPnorm : (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G ⊔ P).Normal)   -- O_{p'}(G)·P ◁ G
    {A : Subgroup G} (hA_le : A ≤ P.normalizer) (hA_p : IsPGroup p A)
    (hPAA : ⁅⁅P, A⁆, A⁆ = (⊥ : Subgroup G)) :                            -- [P,A,A]=1
    (A.subgroupOf P.normalizer).map
        (QuotientGroup.mk' ((Subgroup.centralizer (P : Set G)).subgroupOf P.normalizer))
      ≤ opCore p (↥P.normalizer ⧸ (Subgroup.centralizer (P : Set G)).subgroupOf P.normalizer)
```

確認済の mathlib/repo API:
- `O_p` = `opCore p G` (Ch01), `O_{p'}` = `oPiCore {q|q≠p} G` (Ch03), `O_{p',p}` = `opPpPrimeCore G p` (Ch07 S7B1)
- 三重交換子 `⁅⁅P, A⁆, A⁆` 記法 OK (Ch04 で `⁅⁅H₁,H₂⁆,H₃⁆` 使用)
- **商 `N_G(P)/C_G(P)` は well-formed**: `Subgroup.normal_subgroupOf_centralizer_normalizer`
  (`Mathlib/GroupTheory/Subgroup/Centralizer.lean:164`) が `(centralizer s).subgroupOf (normalizer s)` の
  Normal を **instance** で供給。`normalizerMonoidHom` (ker = `C.subgroupOf N`, L194) で N/C ≅ N(H)→Aut(H) 像。
- ⚠️ **churn 注意点**: instance は `s : Set G` 形 (`centralizer s` / `normalizer s`)。statement の
  `P.normalizer` (Subgroup 形) と `Subgroup.centralizer (P:Set G)` の組合せで Normal instance が
  発火するか要確認 (`normalizer (P:Set G)` 形に揃える必要があるかも)。scaffold build の最初の関門。

### 次の一手 (next session)

1. ✅ (2026-05-29) statement scaffold を `AppA_PStability.lean` に追加 (`thmA4c`, `:= sorry`, build green)。
   **`Subgroup.normalizer` は Set 引数**(Defs.lean:667)なので `Subgroup.normalizer (P : Set G)` で統一 →
   `normal_subgroupOf_centralizer_normalizer` instance (s=↑P) が発火し商 N/C が well-formed になった。
   残: proof 本体 (下記 2,3)。
## A.4(c) proof — Gorenstein 6.5.3 完全引き継ぎ (2026-05-29)

### Gorenstein §6.5 の所在 (特定済)

- **Gorenstein Ch.6 §5「p-stability in p-solvable groups」= `references/gorenstein/finite-groups.mmd` L4758-4823**
  (Ch.7 が L4824 なので §6.5 はこの範囲)。⚠️ Nougat が章を再番号しているので `grep 6.5.x` では出ない。
- **Thm 5.1** (L4762) = 6.5.1: `G` p-solvable, `O_p(G)=1`, (p≥5 or (p=3 ∧ SL(2,3)∉G)) ⇒ `G` p-stable。= A.4(a) の母体 (奇数位数では `thmA4a` で代替済)。
- **Thm 5.2** (L4779) = 6.5.2 = **A.4(b)**: P∈Syl_p of strongly p-solvable G ⇒ 全 normal abelian ≤ O_{p',p}(G)。
- **Thm 5.3** (L4795) = 6.5.3 = **A.4(c)** ← 本命。

### 🎯 重要: A.4(b) は A.4(c) の系 (Gorenstein 5.3 直後 Remark)

> "Taking P to be a Sylow p-subgroup of O_{p',p}(G) ... If Q is an S_p-subgroup of G containing P
> and A is an abelian normal subgroup of Q, then [P,A,A]=1. By the theorem, A⊆P ⊆ O_{p',p}(G).
> **Thus Theorem 5.2 is a special case of Theorem 5.3.**"

⇒ **(c) `thmA4c` を埋めれば (b) `thmA4b` は短い系**。実装順は **(c) → (b)** で確定。

### A.4(c) = Gorenstein 5.3 の証明 (mmd L4801-4815, 翻訳)

`N := N_G(P)`, `C := C_G(P)`。
1. **`P` の N-不変正規列** `P = P_1 ⊃ P_2 ⊃ … ⊃ P_{n+1} = 1`、各 `P̄_i = P_i/P_{i+1}` は
   **elementary abelian** かつ **N が既約に作用**（= P を N-群として見た chief series）。
2. `H_i := ker(N → Aut(P̄_i))` の表現。`N̄_i = N/H_i` は `P̄_i` (Z_p 上ベクトル空間) に
   **faithful + irreducible** に作用 ⇒ **`O_p(N̄_i) = 1`**（Gorenstein 3.1.3）。
3. `[P,A,A]=1` ⇒ 各 `[P̄_i, Ā_i, Ā_i]=1` (`Ā_i` = A の N̄_i での像)。
   **Gorenstein 2.6.6** で各 `x̄ ∈ Ā_i` は `(X-1)²` を満たす（quadratic minpoly）。
   ★ **`N̄_i` は `O_p=1` の奇数位数可解 section ⇒ `thmA4a` (= A.4(a)) で p-stable**
   ⇒ p-stable + quadratic ⇒ `x̄` は `(X-1)` を満たす（自明）⇒ **`Ā_i = 1`** ⇒ `A ⊆ H_i`。
4. ∴ `A ⊆ H := ⋂_i H_i`。`H` は正規列 `P_i` を **stabilize** する。
5. **`H/C ≤ Aut(P)` の chain-stabilizer ⇒ H/C は p-群**（Gorenstein **Cor 5.3.3** = Hall の
   stability theorem: p-群の正規列の stability group は p-群）。
6. `H/C ◁ N/C` かつ p-群 ⇒ `H/C ⊆ O_p(N/C)`。`A ⊆ H` ⇒ **`AC/C ⊆ O_p(N/C)`** ∎。

末尾注: 「Thm 5.3 は p-stable subgroup しか involve しない任意の群で成立」。⇒ 奇数位数仮定は
N̄_i の p-stability (step 3) を `thmA4a` で得るためだけに効く。

### 必要 sub-lemma と repo/mathlib API 候補

| sub-step | 内容 | 候補 |
|---|---|---|
| (1) | p-群 P の N-不変 elementary-abelian chief series | repo `GroupTheory/ChiefFactor.lean`? / `CompositionSeries` を N-群上で。新規の可能性 |
| (2) | faithful irred rep over F_p ⇒ O_p=1 (G 3.1.3) | repo `PGroupFixedVector` (`IsPGroup.invariants_ne_bot`) の対偶系 |
| (3a) | `[V,Ā,Ā]=1` ⇒ 各元 quadratic `(ρx-1)²=0` (G 2.6.6) | 直接計算 (交換子 → minpoly)。repo `S02_Representations` 周辺 |
| (3b) ★ | `N̄_i` p-stable: `thmA4a` 適用 | **`thmA4a` 完成済**。ただし IsPStable は **alg-closed F** 上定義、P̄_i は **F_p** 上 ⇒ **base change (F_p → F_p^alg) で faithful + quadratic 保存** の橋が要る (技術的 sub-lemma、要新規) |
| (4) | H が chain を stabilize ⇒ A ⊆ H | step 3 の帰結 (各 H_i に A) |
| (5) ★ | chain stabilizer ⊆ p-群 (Hall stability, G Cor 5.3.3) | **要調査**: mathlib に stability group 補題があるか / repo Ch.4 coprime + 交換子。無ければ新規 (中規模) |
| (6) | H/C ◁ N/C p-群 ⇒ ⊆ O_p(N/C) | `opCore` の最大正規 p-部分群性質 (Ch01) |

### ⚠️ statement の仮説 discrepancy (要確認)

- Gorenstein 5.3 statement (L4795) は **`O_p(G)P ◁ G`** と書くが、直後 Remark と BG A.4(c)/condition(B)
  は **`O_{p'}(G)P ◁ G`**。Nougat OCR で `p'` → `p` の可能性大。**scaffold は `O_{p'}` (`oPiCore {q|q≠p}`) を採用済**(正)。
- proof 本体 (上記 1-6) は **この仮説をほぼ使っていない**ように見える (N=N_G(P) と section p-stability のみ)。
  → `_hPnorm` が proof で本当に要るか、A.5 application 側の都合かを実装時に判定 (不要なら統合 or 残置)。

### 次セッションの着手順 (推奨)

1. **(5) chain-stabilizer ⊆ p-群** を先に調査・実装 (mathlib 有無 → 無ければ Ch.4 ベース新規)。最大の未知数。
2. **(1) N-不変 chief series** + **(2) O_p=1** を組む (repo ChiefFactor / PGroupFixedVector 活用)。
3. **(3b) base-change bridge** (F_p rep → alg-closed で thmA4a 適用) を実装。
4. 1-6 を assemble して `thmA4c` の sorry を消す。
5. その後 **(b) `thmA4b`** を 5.3 系として短く (Sylow + abelian normal + (c))。
6. notes/bg/appA_pstability.md 更新。

### 再開メモ

- scaffold: `OddOrder/BG/AppA_PStability.lean` の `thmA4c` (statement ~L1360, `sorry` L1372)。
  build: `lake build OddOrder.BG.AppA_PStability` (~20s)。`thmA4a` (= A.4(a)) は同ファイル L1340 付近、完成済。
- 依存定理: `thmA3`/`thmA4a` (同ファイル), `opCore` (Ch01), `oPiCore` (Ch03), `opPpPrimeCore` (Ch07 S7B1),
  `PGroupFixedVector`, `normal_subgroupOf_centralizer_normalizer` (mathlib Centralizer.lean:164)。

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
