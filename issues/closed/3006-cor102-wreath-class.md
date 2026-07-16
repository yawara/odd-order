---
id: 3006
slug: cor102-wreath-class
title: "Cor 10.2: C_p wr C_p の nilpotency class 計算 (WIP 知見付き)"
created: 2026-07-17
---

# Cor 10.2: C_p wr C_p の nilpotency class 計算 (WIP 知見付き)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 目標

Isaacs **Cor 10.2**: `Group.nilpotencyClass ↥P < p` ⇒ `N_G(P)` が p-transfer を
制御 (transfer 像の等式)。証明 = Yoshida 10.1 の対偶 + 「`C_p ≀ C_p` の
nilpotency class = p」+ 準同型像の class 単調性。

## 部品状況

- ✅ `transfer_range_le` (TransferTransitivity.lean, commit 済) — ≠ から < への変換用
- ✅ Yoshida 10.1 / 10.3(c) は landed
- 🚧 `nilpotencyClass_wreath : nilpotencyClass (Mult (ZMod p) ≀ᵣ Mult (ZMod p)) = p`
  — 10.3(c) を base 部分群 (= `rightHom.ker`) に適用する計画。**WIP を revert 済**
  (WreathRecognition.lean は clean な landed 状態)。

## WIP 知見 (再開時に必読)

1. **`set W := Multiplicative (ZMod p) ≀ᵣ ...` (型レベル set) が whnf timeout の
   原因** — 目標に型 let が入り instance 解決が爆発 (memory
   lean-giant-declaration-debugging の既知パターン)。再開時は型を直接書くか
   section-variable にする。
2. 進んだ部品 (revert 前に build 通過確認済のもの):
   `wreathBase := rightHom.ker` / `wreathBase_mul` (成分ごとの積) /
   `wreathBase_pow` / `inl_conj_base` (inl 共役 = left 成分の shift) /
   index = p (`index_ker` + `range_eq_top_of_surjective`, card ⊤ は
   `Subgroup.topEquiv` 経由) / elementary abelian (pow は
   `ZModModule.char_nsmul_eq_zero`) / card = p^p (Lagrange)。
3. 生成部: `a₀ := ⟨Pi.mulSingle 1 (ofAdd 1), 1⟩`;
   f の分解は W が非可換なので `β : (Q → D) →* W`, `g ↦ ⟨g,1⟩` を作り
   Pi-群 (可換) 側で `Finset.univ_prod_mulSingle` → `comap β` で膜性移送。
   単一座標 = `inl q` 共役の `a₀^m` (`ZMod.natCast_rightInverse` で m 決定、
   `← Pi.mulSingle_pow` の向きに注意)。
4. 未解決だった残エラー: `show q⁻¹ * q = 1 by group` が `Inv ℕ` に化ける
   (binder 名衝突の疑い — p : ℕ の q?? 要調査) + whnf timeout (→ 1 の対策で
   解消見込み)。
5. 10.2 本体: hclass < p → by_contra → `transfer_range_le` + `transfer_transfer`
   で v.range ≤ w'.range → ≠ から < → Yoshida → φ : ↥P ↠ W →
   `nilpotencyClass_le_of_surjective` (mathlib 名要確認) → p ≤ class ↥P < p 矛盾。
