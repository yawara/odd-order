---
id: 9402
slug: maximal-class-degree-commutativity
title: "CLAIM: maximal-class p群 (class<p) の positive degree of commutativity — BG E.4 の唯一の gap"
created: 2026-07-21
---

# CLAIM (shared infra): maximal-class p-group の degree of commutativity ≥ 1

**claim 主体**: lane c。**leaf**: 新規 `OddOrder/GroupTheory/MaximalClassPGroup.lean`
(未着手、`RegularPGroup.lean` の class<p 域の sibling)。
**consumer**: `OddOrder/BG/AppE_*.lean` の **BG Prop E.4 abelian clause** (issue 3021、
`AppE_FurtherResults.lean:1657` の sorry)。将来 §16 の maximal-class 論法も候補。

## 何を証明するか

有限 p 群 `S` (p 奇素数) が **maximal class**、かつ **class n < p** のとき、
lower central series `γ_i = S.lowerCentralSeries (i-1)` について
> **positive degree of commutativity**: `⁅γ_i, γ_j⁆ ≤ γ_{i+j+1}` (∀ i,j ≥ 2)
(weight bound `⁅γ_i,γ_j⁆ ≤ γ_{i+j}` を 1 段改善)。

repo の H-indexing (`H_m = iterCommutator T ⊤ m = γ_{m+1}`, T = `C_S(Ω₁(Z₂ S))`) では
`⁅H_a, H_b⁆ ≤ H_{a+b+2}` (a,b ≥ 1)。

## なぜ必要か (issue 3021 (51))

BG Prop E.4 の β 側 eigenvalue supply (E.23) `wᵢ^β ≡ wᵢ^{t₀tⁱ}` は各 level で
`⁅H_{i-1}, T⁆ ≤ H_{i+1}` (= **2-step centralizer relation**) を要する。これは次の
**3-subgroups 帰納**で degree of commutativity に還元される (3021 (51) ②):
`base a=1` = weight bound; `step` は `⁅⁅T,H_{a-1}⁆,⊤⁆ ≤ H_{a+2}` (IH) と
`⁅⁅⊤,T⁆,H_{a-1}⁆ = ⁅H_1,H_{a-1}⁆ ≤ H_{a+2}` (degree of commutativity)。
soft な commutator calculus は `⁅R₀,T⁆ = H_1` の off-by-one で全ルート閉じない (確認済)。

## claim-before-build の事前検索 (2026-07-21)

- repo grep: `IsMaximalClass` / `maximalClass` / `uniserial` / `degreeOfCommut` / `two.?step`
  いずれも**なし** (Explore agent 全数確認)。
- 在るのは: `iterCommutator_eq_lowerCentralSeries` (鎖=lcs, E.8)、weight bound
  (`Mann.lean:791`)、`[S:T]=p`、`γ₂≤T`、coset-counting device
  (`S05_NarrowAutomorphisms.lean:344,421`) — degree of commutativity 本体は未形式化。
- mathlib に maximal class / degree of commutativity なし。
- Coq math-comp/odd-order は App.E 相当を持たない (grep 確認)。
- open 9xxx に重複 claim なし (9400=RegularPGroup E.2, 9401=pRank≤2 は別物)。

⟹ 未構築の genuine shared infra。

## 数学的背景 (⚠ 3021 (52) で精密化 — 下記は (51) の旧見立て)

- 一般の positive dc は **Blackburn 1958** の hard 定理 (associated graded Lie 環の構造定数
  γ_{i,j} が最上反対角 i+j=n で自由、消すのに p odd を使う非線形関係が要る)。**soft でない**。
- ~~class < p ⟹ dc≥1 がクリーン~~ ← **(52) で否定**。class の大小でなく機構が違う。

## ⚠⚠ 2026-07-21 (3021 (52) 由来): gap の真の機構 = **regular B 作用 + Jacobi**

- dc は **H_0=T 込みの `⁅H_a,H_b⁆≤H_{a+b+2}` (∀a,b≥0) が丸ごと本体** (soft な小 core 還元なし)。
- ⭐ **B 作用 (abelian regular, 相異なる固有指標 χ_Q≠χ_T on S/S')** が各 level の
  **clean な二者択一** (Case A `t·` / Case B `t₀·`) を eigenvalue 論だけで与える (Jacobi 不要、
  形式化可能)。
- ⚠ 但し「全 level Case A (dc≥1)」の解決 = 「no switch」は **Jacobi と絡む hard core**。
  distinct-eigenvalue + Jacobi ⟹ dc≥1 が成り立つ**らしい** (dc=0 構成が全て Jacobi 違反、
  3021 (52) ③で実例確認) が clean proof 未確立。Blackburn の dc=0 群が regular B 作用を
  許さないのが真相と思われる。
- ⟹ **class<p は理由でない**。authoritative input (Blackburn 分類 / FT1991 原論文 / 最強モデル) 待ち。

## 構造定数 setup (Lie 環、形式化の設計候補)

`L = ⊕ Lⱼ`、`L₁ = ⟨a,b⟩` (a = uniserial 生成元 v̄, b = w̄₀ = T 方向)、`Lⱼ = ⟨eⱼ⟩` (j≥2, 1 次元)。
`eⱼ = (ad a)^{j-1}(b)` (e₁:=b), `⁅a, eⱼ⁆ = e_{j+1}` (uniserial)、`⁅eᵢ,eⱼ⁆ = γ_{i,j} e_{i+j}`。
- (R1) `γ_{i,j} = γ_{i+1,j} + γ_{i,j+1}` (ad a derivation), i,j≥1。
- (R2) `γ_{i,j} = -γ_{j,i}` (antisymmetry)。
- (R4) `γ_{i,j}·γ_{1,i+j} = γ_{1,i}·γ_{i+1,j} + γ_{1,j}·γ_{i,j+1}` (ad b derivation, 非線形)。
- boundary `γ_{i,j}=0` (i+j>n)。goal: `γ_{i,j}=0` (i,j≥2) ⟺ `γ_{2,j}=0` (j≥2、R1+R2 で伝播)。

⚠ 形式化は Lie 環を建てるより **群の iterCommutator で直接** `⁅H_a,H_b⁆≤H_{a+b+2}` を
証明する方が軽い可能性 (associated graded Lie ring infra を作らずに済む)。着手時に決める。

## 進め方

1. **[最強モデルで clean proof 確認]** class<p (p≥2n+3) の dc≥1 の proof strategy を
   ChatGPT (最強モデル、Chrome MCP) で確定 ([[feedback-ask-chatgpt-for-elided-gaps]])。
   数学は未解決でなく (dc≥1 は本 setup で真)、正しい・形式化しやすい proof の確定待ち。
2. **[群で直接 or Lie 環]** dc≥1 = `⁅H_a,H_b⁆≤H_{a+b+2}` を形式化。
3. **[還元]** 3-subgroups 帰納で `⁅T,H_a⁆≤H_{a+2}` (3021 (51) ②)。
4. **[assemble]** `caseA_eigenvalue_step` を base+step で帰納 → `hβsupply` →
   `commutator_centralizer_eq_bot_of_beta_supply` → E.4 abelian clause (3021 の残 sorry)。

## 完了条件

`⁅H_a,H_b⁆≤H_{a+b+2}` (a,b≥1、maximal class + class<p) が sorry-free / axiom-clean。
下流 3021 の E.4 abelian clause が解錠。本 claim を close。
