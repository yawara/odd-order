---
id: 4
slug: isaacs-3-22-pilength-placeholder
title: "Isaacs Thm 3.22 (π-length ≤ 1) の fake True placeholder を正式 statement に置換"
created: 2026-05-24
---

# Isaacs Thm 3.22 (π-length ≤ 1) の fake True placeholder を正式 statement に置換

## 背景

[Ch03_SplitExtensions.lean:1884](../OddOrder/Isaacs/Ch03_SplitExtensions.lean) の
`piLength_le_one_of_abelian_pi_hall` は現状 fake placeholder:

```lean
theorem piLength_le_one_of_abelian_pi_hall [Finite G] (π : Set ℕ)
    (_hπsep : IsPiSeparable π G)
    (_hAb : ∀ (H : Subgroup G) (_ : IsHallSubgroup π H), ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    True := by  -- TODO: π-length の正式定義後に書き直す
  trivial
```

戻り値が `True` で type-check が空回り. docstring と statement が一致しておらず,
将来下流から呼ばれたら破綻する.

書籍 (Isaacs FGT p.95) では Thm 3.22 は
「G π-separable + abelian な π-Hall ⇒ `[O_{π',π}(G), O_{π',π}(G)] ≤ O_{π'}(G)`」
= π-length ≤ 1 と同値.

なお [issues/0005](issues/0005-isaacs-3d-pi-separable-redefine.md) (`IsPiSeparable` 暫定定義
の置換) が prerequisite. 正式 `IsPiSeparable` が無いと statement が意味を持たない.

## やること

- [ ] 先に issue 0005 (`IsPiSeparable` の正式定義) を解決
- [ ] π-length の正式定義: `def piLength (π : Set ℕ) (G : Type*) : ℕ` を導入
      (Isaacs 流: `O_π O_π' O_π O_π' ... = G` となる最小 n / 2)
- [ ] `piLength_le_one_of_abelian_pi_hall` の戻り値型を `True` から
      `piLength π G ≤ 1` (または同値の `⁅O_{π',π}(G), O_{π',π}(G)⁆ ≤ oPiCore πᶜ G`) に変更
- [ ] 証明本体を Isaacs 流 (Hall-Higman 1.2.3 + abelian Hall の特殊化) で実装
- [ ] AxiomsCheck flagship に追加 (Hall-Higman 1.2.3 の直系応用なので価値あり)

## 完了条件

- `piLength_le_one_of_abelian_pi_hall` の戻り値型が `True` でない
- 実 body が `trivial` でなく, 数学的内容を持つ証明
- `lake build` が通る

## 参照

- [Ch03_SplitExtensions.lean:1884](../OddOrder/Isaacs/Ch03_SplitExtensions.lean)
- [notes/isaacs/ch03_split.md](../notes/isaacs/ch03_split.md) §3D
- Isaacs FGT p.95 (Thm 3.22)
- 前提 issue: 0005 (`IsPiSeparable` 暫定定義の置換)
