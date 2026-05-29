---
id: 49
slug: bg-appa-a5
title: "BG App.A Thm A.5 — stability of P-normalized abelian p-groups (thmA5)"
created: 2026-05-29
---

# BG App.A Thm A.5 — stability of P-normalized abelian p-groups (thmA5)

## 背景

issue [#0047](closed/0047-bg-appa-a4.md) で A.4(a/b/c) を完成 (sorry-free, axiom-clean)。
App.A 連鎖の次ゲート = **A.5**。`Thm 6.2 ⟸ App.B B.4 ⟸ A.5 ⟸ A.4(c) ✅` の本線で、
App.B (Puig L(S)) の唯一の実質依存 (route note `bg_s6_appAB_route_2026_05_28.md`)。

投資調査 workflow `appA-to-thm62-investigation` (run wf_612ed4a4-224) + App.B mmd 精読で
X-signature と proof 構造を確定済 (下記)。**新規ブロッカー Prop 1.10 は完成済**
(`coprime_nilpotent_acts_trivially_of_centralizer_self`, S01)。

## Statement (BG mmd L4488-4513)

`p` 奇素数, `G` solvable odd order, `P` を `G` の**正規** `p`-部分群, `X` を
「`P` で正規化される abelian `p`-群たち」で生成される `G` の部分群とする。このとき:

- **(1)** `X·C_G(P)/C_G(P) ⊆ O_p(G/C_G(P))`
- **(2)** `O_{p'}(G)=1` ∧ `C_{O_p(G)}(P) ⊆ P` ⇒ `X ⊆ O_p(G)`

## X-signature 確定 (App.B B.3/B.4 整合, 2026-05-29)

A.5 の `X` は B.3/B.4 で次のように消費される (mmd L4644-4757):

- **B.3**: `P := L_{2n+1}(T)` (正規 p-部分群), `X := L_{2n+2}(S)` で **A.5(2)**
  (`O_{p'}=1`, `C_T(L_{2n+1}(T)) ⊆ L_{2n+1}(T)` = B.1(f)) ⇒ `L_{2n+2}(S) ⊆ T=O_p(G)`。
- **B.4 Step3**: `P := Y = Z(L(T))` (abelian normal), `X := L(S)` で **A.5(1)**。

両者とも生成 abelian 部分群は `S` 内 (= p-群)。Puig の `P → X` (X が P-正規化 abelian 部分群で
生成) から `X ≤ ⨆ {abelian p-grp normalized by P}` が出る。⇒ **A.5 の仮説は `≤` 形が最も柔軟**:

```lean
hX : X ≤ ⨆ A ∈ {A : Subgroup G | A.IsCommutative ∧ IsPGroup p ↥A
        ∧ P ≤ Subgroup.normalizer (A : Set G)}, A
```

(`=` でなく `≤`。part(1) は sup の像が O_p(G/C) に入るので X の像も入る。B.3/B.4 は
`P→X` から `X ≤ sup` を供給。Puig `L_G`/`→` machinery は App.B で別途定義し、ここでは
self-contained な sup 仮説に留める。)

## Proof 構造 (mmd L4496-4513, 確定)

`G = N_G(P)` (P 正規)。`C := C_G(P)`。

- **part(1)**: 各 abelian p-群 `A` (P-正規化) に `[P,A,A] ⊆ [A,A] = 1` で **A.4(c) `thmA4c`**
  適用 ⇒ `AC/C ⊆ O_p(G/C)`。X ≤ ⨆ A なので `XC/C ⊆ O_p(G/C)`。
  ⚠ **最大の機械コスト = thmA4c の出力 (↥N_G(P)/(C.subgroupOf N) 上) を P 正規 (N_G(P)=⊤≃*G)
  で G/C へ transport** (`Subgroup.topEquiv` + opCore の MulEquiv 保存)。
- **part(2)**: `Q := O_p(G)`。`O_{p'}=1` ⇒ `Q = O_{p',p}(G)`, `P ⊆ Q`。
  **Prop 1.15(b)** = `hall_higman_solvable_specialization` (S01) で `C_G(Q) ⊆ Q`。
  各 p'-元 `u ∈ C`: `C_Q(C_Q(u)) ⊆ C_Q(P) = C∩Q ⊆ P ⊆ C_Q(u)` ⇒ **Prop 1.10 ✅**
  (`coprime_nilpotent_acts_trivially_of_centralizer_self`, ⟨u⟩ の Q 上共役作用) で u が Q を中心化
  ⇒ `C_G(Q)⊆Q` で u=1 ⇒ C は p-群 ⇒ `C ◁ G` で `C ⊆ O_p(G)=Q`。
  `C ⊆ Q` ⇒ `O_p(G/C) = O_p(G)/C` ⇒ part(1) と合わせ `X ⊆ Q`。

## やること

- [x] **X-signature の sup を Lean で定義/確認** — ✅ `X ≤ ⨆ A ∈ {IsMulCommutative ↥A ∧
  IsPGroup p ↥A ∧ P ≤ normalizer ↑A}, A` で確定。
- [x] **part(1) `thmA5_part1`** — ✅ **2026-05-29 完成 (sorry-free, axiom-clean)**。
  ⭐ **簡略化**: N_G(P)=⊤ transport は**不要だった** — P 正規なので `thmA4c` (N_G(P) 経由) でなく
  **`stabilityLiftAux` を M:=G, K:=P で直接適用**できる (1 行)。各生成子 A に `⁅⁅P,A⁆,A⁆=⊥`
  (P≤N(A) で ⁅P,A⁆≤A, A abelian で ⁅A,A⁆=⊥) → stabilityLiftAux → iSup で X に持ち上げ。
- [ ] **part(2) `thmA5_part2`**: `O_{p'}=1` ∧ `C_{O_p(G)}(P)⊆P` ⇒ `X ⊆ O_p(G)`。
  Q:=O_p(G), C:=C_G(P)。各 p'-元 u∈C に Prop 1.10 (✅, ⟨u⟩ の Q 上共役作用
  `(MulAut.conjNormal (H:=Q)).comp (zpowers u).subtype`) で u が Q 中心化 ⇒ C_G(Q)⊆Q (Hall-Higman)
  で u=1 ⇒ C は p-群 ⇒ C◁G で C⊆Q。`O_p(G/C)=O_p(G)/C` (C⊆Q 商対応) + part(1) で X⊆Q。
  **残: conjNormal→fixedPoints=C_Q(u) 翻訳 + Q-内部 centralizer chain + opCore 商対応 (~100 行)。**
- [ ] `thmA5` (part1+part2) を統合 (or part2 が X⊆O_p を直接与えるので part2 = 本体)。
- [ ] `AxiomsCheck.lean` に登録。

## 必要 API (確認済)

- `OddOrder.BG.AppA.thmA4c` (sorry-free ✅), `thmA4a`, `stabilityLiftAux` (AppA)
- `OddOrder.BG.Ch1.S01.coprime_nilpotent_acts_trivially_of_centralizer_self` (Prop 1.10 ✅)
- `OddOrder.BG.Ch1.S01.hall_higman_solvable_specialization` (Prop 1.15(b) ⊆ O_p, ✅)
- `Subgroup.topEquiv`, `Subgroup.normalizer (P:Set G)`, `MulAut.conjNormal` (AppA:1441 bridge)
- `O_p(G/C) = O_p(G)/C` (C ◁ G, C ⊆ O_p): 新規小補題 or mathlib (S7B1 `opCore_map_mk_oPiCore_eq_bot` 近縁)
- 内部共役作用 ⟨u⟩↷Q を `(MulAut.conjNormal (H:=Q)).comp (zpowers u).subtype` で外部化 (Prop 1.10 適用用)

## 完了条件

- `thmA5` (part1+part2 or 統合) を `OddOrder/BG/AppA_PStability.lean` に sorry-free 追加。
- `lake build OddOrder` green, axiom-clean。
- 後続 App.B B.3/B.4 が `X ≤ ⨆ ...` 仮説経由で A.5 を呼べる状態。

## 参照

- BG mmd L4488-4513 (A.5 statement + proof), L4517-4757 (App.B: L(S) 定義 + B.1-B.4)
- closed [#0047](closed/0047-bg-appa-a4.md) (A.4 a/b/c), workflow run wf_612ed4a4-224 (調査プラン)
- notes: [`bg_s6_appAB_route_2026_05_28.md`](../notes/meta/bg_s6_appAB_route_2026_05_28.md),
  [`appA_pstability.md`](../notes/bg/appA_pstability.md), [`appB_puig.md`](../notes/bg/appB_puig.md)
- repo: `AppA_PStability.lean` (thmA4c/stabilityLiftAux), `S01_Solvable.lean` (Prop 1.10/Hall-Higman)
