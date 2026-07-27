---
id: 158
slug: six-three-quotient-nilpotent
title: "Pf (6.3)/(6.5) の冪零仮説を書籍どおり H/M へ弱める (repo は H 冪零)"
created: 2026-07-27
---

# Pf (6.3)/(6.5) の冪零仮説を書籍どおり `H/M` へ弱める

## 書籍 (p. 30-31、`04.8_pp_30_37_Some_Coherence_Theorems.txt` L27/L56)

> **(6.3) Theorem.** Assume Hypothesis (6.1).  Let `M, H, H₁` be normal subgroups of `L` such that
> `M ⊆ H₁ ⊆ H ⊆ K`.  Assume further that
> **(a) `H/M` is nilpotent**, (b) `𝒮(H₁)` is coherent, (c) `|H:H₁| > 4|L:K|² + 1`.
> Then `𝒮(M)` is coherent.

> **(6.4) Hypothesis.** … (b) Let `M` be a normal subgroup of `L` contained in `K` such that
> **`K/M` is nilpotent**.

⟹ 書籍が要求するのは**商 `H/M` の冪零性**。

## repo の現状 — `H` 自身の冪零性を要求

`S08_Theorem62_63_Standalone.lean:120` (および `:391` の bundled 版):

```lean
theorem six_three_descent
    {K H M H₁ : Subgroup ↥L} [Group.IsNilpotent ↥H] [IsSolvable ↥K]   -- ⚠ H 自身
```

`H` 冪零 ⟹ `H/M` 冪零 だが逆は成り立たないので、**書籍より狭い**。
survey「残っている特殊化」項目 3 の実体。

## 冪零性の使用箇所は 1 点だけ (実測)

`six_three_descent` の証明本体で冪零性が効くのは

```lean
    have hcentral := normal_central_of_maximal_normal_below (H := H) (A := A) (B := B)
      hHnorm hAltH.le hBltA hBmaxl
```

の 1 箇所のみ (`S08_Theorem62_63_Standalone:163`)。その補題
(`S08_YsetInner.lean:110`) は `[Group.IsNilpotent ↥H]` を取り、内部では

```lean
  have hinf := isNilpotent_normal_inf_center_ne_bot ...   -- Γ = ↥H ⧸ B.subgroupOf H
```

で **`H/B` の冪零性しか使っていない** (`[Group.IsNilpotent ↥H]` から instance 合成で得ている)。

書籍の論法もそこ: 「Since `H/M` is nilpotent, we have `(A/B) ∩ Z(H/B) ≠ 1`」。
`M ≤ B` なので `H/B` は `H/M` の商 ⟹ `H/M` 冪零から `H/B` 冪零が出る
(`Group.nilpotent_of_surjective`, `Mathlib/GroupTheory/Nilpotent.lean:762`)。

## やること

1. `normal_central_of_maximal_normal_below` の仮説を
   `[Group.IsNilpotent ↥H]` → `[Group.IsNilpotent (↥H ⧸ B.subgroupOf H)]` に弱める。
   ⚠ **binder の障害は「順序」だけだった (2026-07-27 訂正)**: 商型 `↥H ⧸ B.subgroupOf H` の
   `Group` instance には `(B.subgroupOf H).Normal` が要るが、これは
   **`Subgroup.normal_subgroupOf` という instance が mathlib に在る**
   (`Mathlib/Algebra/Group/Subgroup/Basic.lean:906`, `[N.Normal] → (N.subgroupOf H).Normal`)。
   最初の試行が失敗したのは、冪零性 binder を `[B.Normal]` より**前**に置いていたため
   (その時点では `B.Normal` がまだ scope に無い)。`[A.Normal] [B.Normal]` の**後ろ**に
   置けば通る。明示の instance binder も呼び出し側の `haveI` も不要で、
   **3 つの呼び出し箇所は無変更**。
   (当初 `Subgroup.Normal.subgroupOf` が theorem だから不可、と書いたのは誤り —
   同名の theorem 版と instance 版が両方ある。)
2. `six_three_descent` (と `:391` の bundled 版) の `[Group.IsNilpotent ↥H]` を
   `(hHM : Group.IsNilpotent (↥H ⧸ M.subgroupOf H))` に置換し、call 直前で
   `Group.nilpotent_of_surjective` により `H/B` の冪零性を作る
   (`H/M ↠ H/B` は `M ≤ B` から)。
3. 旧版は `H` 冪零からの 1 行特殊化として残す (下流 consumer 無変更)。
4. AxiomsCheck 更新 + survey の「残っている特殊化」項目 3 を更新。

## ✅ 完了 (2026-07-27)

`six_three_descent` / `six_three_of_six_two_oracle` がともに
`[Group.IsNilpotent (↥H ⧸ M.subgroupOf H)]` (書籍 (6.3)(a) そのもの) で成立。
`normal_central_of_maximal_normal_below` も `[Group.IsNilpotent (↥H ⧸ B.subgroupOf H)]` へ弱化。
`M ≤ B` から `H/M ↠ H/B` を作り `Group.nilpotent_of_surjective` で `H/B` の冪零性を供給する。

**下流 consumer は全て無変更** — `H` 冪零を持つ呼び出し側では、商の冪零性も
`(M.subgroupOf H).Normal` も instance 合成で自動的に得られるため。

## 完了条件

`six_three_descent` が `H/M` 冪零だけで成立し、旧 `H` 冪零版がその特殊化になること。
build green + AxiomsCheck OK + lint --strict clean + sorry 非退行。
