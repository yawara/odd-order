---
id: 5
slug: isaacs-3d-pi-separable-redefine
title: "Isaacs §3D IsPiSeparable 暫定定義 (IsSolvable) を正式定義に置換"
created: 2026-05-24
---

# Isaacs §3D IsPiSeparable 暫定定義 (IsSolvable) を正式定義に置換

## 背景

[Ch03_SplitExtensions/Main.lean:1238](../../OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean) の `IsPiSeparable` は
現状 暫定定義:

```lean
def IsPiSeparable (_π : Set ℕ) (G : Type*) [Group G] : Prop := IsSolvable G
```

`_π` 引数を完全に無視している. このため:

- **Thm 3.20** (`hall_exists_of_piSeparable`): π-separable ⇒ Hall π subgroup 存在.
  暫定定義下では実質「solvable ⇒ Hall π」(Thm 3.13 Hall-E と同じ) に縮退.
- **Thm 3.21** (`hall_higman_1_2_3`): π-separable + `O_π'(G) = ⊥` ⇒ `C_G(O_π(G)) ≤ O_π(G)`.
  暫定定義下では仮定が「solvable」に縮退するが, Hall-Higman 1.2.3 は π-separable 一般で
  成立するので, 正式定義に差し替えれば仮定が緩む.
- **Thm 3.22** (`piLength_le_one_of_abelian_pi_hall`): fake `True` placeholder. issue 0004 で対応.

正式定義 (Isaacs FGT p.89 Def 3.18): 群 `G` が π-separable とは,
G の composition factor が全て π-group か π'-group であること.

mathlib に直接対応無し (`IsSolvable` を `derivedSeries` で定義したのと同様, 自前で書く必要あり).

## やること

- [ ] Isaacs Def 3.18 を Lean で実装. 候補形:
  - **A**: composition series + 各 factor の π / π' 判定 (mathlib `CompositionSeries`).
  - **B**: 正規列 + 各商の π-group か π'-group (Isaacs 流に近い, mathlib `Series` 系で).
  - **C**: `|G|`-induction で `oPiCore π G ≠ ⊥` or `oPiCore π' G ≠ ⊥` を継承で要求.
- [ ] 暫定定義との同値性 (solvable ⇒ π-separable ∀ π) を補題化
- [ ] Thm 3.18 (π-separable の補助補題), Thm 3.19 (G solvable ⇒ 全 π について π-separable),
      Thm 3.20 (π-separable ⇒ Hall π) を新定義下で書き直す
- [ ] Thm 3.21 Hall-Higman 1.2.3 の証明本体を新定義に対応させる (現行証明は solvable
      しか使っていない可能性が高いので, induction を π-separable で回せば自然に通るはず)
- [ ] [`notes/isaacs/ch03_split.md`](../../notes/isaacs/ch03_split.md) §3D の対応表を更新

## 完了条件

- `def IsPiSeparable` が `:= IsSolvable G` でなく, π を実際に使う定義になる
- `lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` が通る
- `lake build OddOrder.AxiomsCheck` が通る (Hall-Higman 1.2.3 flagship が新定義で unconditional)

## 参照

- [Ch03_SplitExtensions/Main.lean:1238](../../OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean) (暫定 def)
- [Ch03_SplitExtensions/Main.lean:1556](../../OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean) (`isPiSeparable_of_solvable`)
- [Ch03_SplitExtensions/Main.lean:1808](../../OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean) (`hall_higman_1_2_3`)
- [notes/isaacs/ch03_split.md](../../notes/isaacs/ch03_split.md) §3D
- Isaacs FGT pp.89-95 (§3D)
- 関連 issue: 0004 (Thm 3.22 fake placeholder; 本 issue が前提)
