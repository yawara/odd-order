---
id: 3022
slug: bg-thm157e-vacuous
title: "BG Thm 15.7(e) の条項が論理的に vacuous — book strength で言い直す"
created: 2026-07-18
---

# BG Thm 15.7(e): 現在の条項は恒真 (情報ゼロ)

## 発見 (2026-07-18、specialized 債務の棚卸し中に判明・hub が独立検証)

`OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/OpicoreCentralizer.lean:361` の
`fitting_not_ti_cases` の結論は:

```lean
(S14.IsTypeF M ∨ S14.IsTypeP1 M) ∧                    -- (a) …:363
  MF M = Msigma M ∧
  ∃ X, … ∧ derivedInG M ≤ fittingInAmbient M ∧
    (∃ p, p.Prime ∧ p ∈ σ(M) ∧ p ∉ β(M) ∧
      (IsMulCommutative ↥(MF M) ∨                      -- (e) …:377
        ¬ IsMulCommutative ↥(MF M) ∧
          (S14.IsTypeF M ∨ S14.IsTypeP1 M)))           -- ← (a) と同一 …:379
```

末尾 (e) は `A ∨ (¬A ∧ B)` の形で、`B = IsTypeF M ∨ IsTypeP1 M` は**同じ定理の conjunct (a) が
既に与える**。よって consumer 側では `A ∨ ¬A` (排中律) に潰れ、**(e) は情報を一切運ばない**。

⚠ **定理自体は真**であり sorry も無い。問題は「book の条項 (e) を形式化した」と数えられないこと
([[scaffold-sorry-free-not-done]] の系: sorry-free でも内容ゼロなら doneness でない)。

## やること

- [ ] BG mmd の Thm 15.7(e) 原文を読み、(e) が**実際に主張している内容**を特定する
      (現在の Lean 版は `IsMulCommutative (MF M)` の場合分けを述べているつもりだが、
      (a) の存在下で自明化している ⟹ 原文は (a) と独立な追加情報を述べているはず)。
- [ ] 非自明な形に言い直して証明する。典型的には (e) の第2枝が (a) の再掲でなく
      **`M_F` 非可換の場合に固有の構造** (型ごとの追加条件) を述べる形になるはず。
- [ ] 言い直しが原文どおり非自明であることを確認 (`A ∨ (¬A ∧ B)` に潰れないこと)。
- [ ] survey の BG §15 特殊化債務欄を更新。

## 完了条件

(e) が (a) から独立な内容を主張し、book strength・sorry-free・axiom-clean で証明されること。
⚠ 現状の恒真版を「証明済」と数えない。

## 参照
- `S15_MF/OpicoreCentralizer.lean:361-379`、BG mmd の Thm 15.7。
- 本件は survey にも注記済 (BG §15 の特殊化債務欄)。
- 類似の「真だが内容ゼロ」パターン: App.D の旧 `cnTheorem_reduction`、NearFields の旧
  `∃ classification : Prop, classification` (いずれも本 session で de-opacify 済)。
