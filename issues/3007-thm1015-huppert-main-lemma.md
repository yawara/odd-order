---
id: 3007
slug: thm1015-huppert-main-lemma
title: "Thm 10.15/10.12: Huppert metacyclic main lemma (部品確認済)"
created: 2026-07-17
---

# Thm 10.15/10.12: Huppert metacyclic main lemma

## 目標

- **Thm 10.15**: `P ⊴ N`, `P ∈ Syl_p(N)`, `P` nonabelian metacyclic, `p > 2`
  ⇒ `p ∣ (commutator N).index`。新 leaf
  `OddOrder/Isaacs/Ch10_MoreTransfer/HuppertMetacyclic.lean`。
- **Thm 10.12 (Huppert)**: `P ∈ Syl_p(G)` nonabelian metacyclic, `p > 2` ⇒
  `p ∣ |G:G'|`。10.14 (`not_surjective_wreath_of_isMetacyclic`, landed) +
  Yoshida 10.1 対偶 (Cor 10.2 と同型の argument) + 10.15 (N = N_G(P) に適用)。
  transfer 側 bridge: v(G) range = w'(N) range (Cor 10.2 の証明パターン,
  `transfer_range_eq_of_nilpotencyClass_lt` 参照) から
  「p ∣ |N:N'| ⇒ p ∣ |G:G'|」を導く部分は要設計 (Isaacs は A^p(G) 言語;
  Lean では transfer range nontriviality 経由で書く)。
- **Thm 10.16** (Maschke 一般版, u ↦ u^m bijective): OperatorMaschke.lean に追加
  (10.17 既存 = `exists_aInvariant_complement_of_isElementaryAbelian` の一般化)。
  10.15 には不要 (10.17 で足りる) だが番号付き結果なので形式化対象。
  一般化原則 [[feedback-generalize-specialized-fully]] により Isaacs 原文の形
  (V = U × W, U abelian K-invariant, u ↦ u^m 全単射) で。

## 部品 (2026-07-17 確認済)

| ステップ | 部品 | 所在 |
|---|---|---|
| V = Ω₁(P) elem ab, \|V\| = p² | `isElementaryAbelian_omega1_of_isMetacyclic` (BG 4.10) | S04_SmallRankBasic:1536 |
| Ω₁ characteristic | `Omega.characteristic` instance | OmegaSubgroup:90 |
| x^p = 1 ⇒ x ∈ Ω₁ | `Omega.mem_of_pow_eq_one` | OmegaSubgroup:70 |
| 6.11 odd 形 (unique order-p ⇒ cyclic) | `isCyclic_of_subgroups_card_prime_unique_of_odd` | Ch06 Main:1262 |
| Aut(cyclic) abelian | `IsCyclic.mulAutMulEquiv` + `commGroupOfInjective` idiom | DQSDRecognition:519 の証明 |
| N/C ↪ Aut(H) | `MulAut.conjNormal` + `QuotientGroup.lift` idiom | DQSDRecognition:498 の証明 |
| Maschke coprime 版 (10.17) | `exists_aInvariant_complement_of_isElementaryAbelian` | OperatorMaschke:287 |
| IsAInvariant interface | Isaacs Ch03 Main:744 (`φ : A →* MulAut E`) | 使用例 = S04b_Thm412 |
| metacyclic 閉包 | `IsMetacyclic.subgroup` / `.of_surjective` / `.isCyclic_commutator` | IsMetacyclic.lean |
| 10.14 | `not_surjective_wreath_of_isMetacyclic` | WreathRecognition 末尾 |

## 未確認 (次 session 冒頭に)

- [ ] normal order-p subgroup of p-group is central (P' ≤ Z(P) step) — mathlib/repo grep
- [ ] cyclic p-group の unique subgroup of order p (existence + uniqueness)
- [ ] characteristic ⊴ normal ⇒ normal (P' char P ⊴ N) の mathlib 名
- [ ] N ↷ V (V ⊆ Z(P) 時 P ≤ ker) → N/P →* MulAut ↥V の lift 構成
  (S04b_Thm412 の OperatorMaschke 使用例を precedent に)

## 証明骨子 (Isaacs pp. 305-306, mmd L5613-5645)

1. 帰納 on Nat.card P (strong induction)。任意の Y ⊴ N, |Y| = p:
   P/Y ⊴ N/Y は Sylow + metacyclic (10.13(a))。nonabelian なら帰納 ⇒
   p ∣ |N/Y : (N/Y)'| ⇒ p ∣ |N:N'| (surjection N ↠ N/Y ↠ (N/Y)^ab)。
2. 否なら全 Y で P/Y abelian ⇒ P' ≤ Y ⇒ Y = P' ⇒ |P'| = p、P' = N の唯一の
   normal order-p subgroup。(Y₀ = P' cyclic の unique order-p subgroup、char P' ⊴ N)
3. |P'| = p ⇒ P' ≤ Z(P) (class 2)。
4. V := Ω₁(P): BG 4.10 (P noncyclic ← nonabelian) ⇒ elem ab, |V| = p²、V ⊴ N (char)。
5. V ⊆ Z(P) と仮定 → N/P ↷ V coprime、P' invariant ⇒ 10.17 ⇒ V = P' × W,
   W ⊴ N, |W| = p, W ≠ P' → (2) の一意性と矛盾 ⇒ V ⊄ Z(P)。
6. P/Z elementary abelian (y^p ∈ Z: [y^p,x] = [y,x]^p = 1)。
7. N/P ↷ P/Z coprime、VZ/Z invariant ⇒ 10.17 ⇒ P/Z = (VZ/Z) × (H/Z)、H ⊴ N。
8. V ∩ H ≤ VZ ∩ H = Z ∩ V …: |V ∩ H| < p² ⇒ H の order-p subgroup は
   V ∩ H 内で一意 ⇒ 6.11 ⇒ H cyclic。
9. VZ abelian ≠ P ⇒ H/Z ≠ 1 ⇒ H ⊄ Z(P) 側 ⇒ P ⊄ C := C_N(H)。
10. N/C ↪ Aut(H) abelian ⇒ N' ≤ C; p ∣ |N:C| (P ⊄ C, C ⊇ ker で p-element 生存)
    ⇒ p ∣ |N:N'| (`Subgroup.index_dvd_of_le`)。

## 完了条件

- HuppertMetacyclic.lean: 10.15 + 10.12 sorry-free
- OperatorMaschke.lean: 10.16 一般版
- ch10 note §10B 更新
