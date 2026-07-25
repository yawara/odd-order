---
id: 9503
slug: hall-wielandt-abelian-weakly-closed
title: "Hall-Wielandt (p>2, A abelian weakly closed) — Pf II (17) 用"
created: 2026-07-26
---

# Hall-Wielandt (p>2, A abelian weakly closed) — Pf II (17) 用

## 🔒 CLAIM (shared infra, hub band 9500)

**claimed by: main/hub session (issue 2053 = Pf Part II Ch.II Theorem B の駆動)**、
2026-07-26。着手前に他レーンが同種の infra を建てていないか
`ls issues/9*.md` + `grep -rn "weakly closed\|Hall.Wielandt" OddOrder/` で実測済
(2026-07-26 時点でヒット無し。既存の近縁は下記「repo 実測」の 2 件のみ)。

## 背景

Peterfalvi Part II Ch.II step (17) (p. 114) の結論が使う唯一の未形式化 infra:

> The subgroup `Z₁PΣ` of `G` is thus weakly closed in `R₂` and, as `Z₁PΣ` is abelian,
> we obtain `G/O³(G) ≅ R₂⟨s⟩/O³(R₂⟨s⟩)` by the Hall-Wielandt Theorem.

statement (Peterfalvi p. 108 に明記、[Ha] Thm 14.4.2):

> `P` を Sylow `p`、`A` を `P` 内で `G` に関し weakly closed とする。
> `A ⊆ Z_{p−1}(P)` または (`p > 2` かつ `A` abelian) ならば
> `G/O^p(G) ≅ N_G(A)/O^p(N_G(A))`。

(17) が要るのは **`p > 2` ∧ `A` abelian** の枝 (`A = Z₁PΣ` は位数 27 の初等可換、
`p = 3`)。`A ⊆ Z_{p−1}(P)` 枝は不要。

## repo 実測 (2026-07-26)

- ✅ `OddOrder.Isaacs.Ch10.transfer_range_eq_of_nilpotencyClass_lt`
  (`Isaacs/Ch10_MoreTransfer/Yoshida.lean:509`, "Hall-Wielandt strengthening via
  Yoshida"): **class(Sylow) < p** のときの版。step (12) が実際に消費している
  (`StepTwelveTransfer.lean:125`) が、(17) では Sylow = `R₂` の class が
  `< 3` とは限らない (`R̄₁ = R₁/Z₁` が class ≤ 2 ⟹ `R₁` は class ≤ 3) ので**使えない**。
- ✅ transfer 基盤一式: `OddOrder.GroupTheory.transfer_range_le` /
  `transfer_transfer` / `transferRes` / `transfer_abelianization_range_eq_bot`
  ((B2) から G-transfer 自明を出す部品、step (12) が使用) /
  `MackeyTransfer.lean` / `TransferInvariantTransversal.lean` (step (9) 用)。
- ❌ weakly closed の定義そのもの、Grün の第二定理、focal subgroup の一般形は無い
  (`grep "weakly closed\|weaklyClosed"` はヒット無し。Isaacs は演習 5C.6 のみで
  本文に無い)。

## やること

- [ ] `weaklyClosed` の定義 (`A ≤ P` かつ `∀ g, A^g ≤ P → A^g = A`) を
      `OddOrder/GroupTheory/` に新設 (leaf 名は `WeaklyClosed.lean` 想定)
- [ ] 主定理: `p` 奇素数、`P : Sylow p G`、`A ≤ P` abelian かつ `P` 内で weakly closed
      ⟹ `N_G(A)` が `p`-transfer を制御する形 (step (12) の消費形に合わせ、
      **transfer の range 一致** `v(G) = w(N_G(A))` として述べるのが実用的)
- [ ] (17) 側の消費形: (B2) (`p ∤ |G^ab|`) と併せて
      「`N_G(A) = R₂⟨s⟩` が位数 3 の商を持つ ⟹ `G` も位数 p の商を持つ ⟹ (B2) 矛盾」
      が出る形に整える
- [ ] AxiomsCheck 登録

## 証明方針 (未確定、着手時に精査)

古典的には **Grün の第二定理** (weakly closed abelian `A` ⟹ `N_G(A)` が p-transfer を
制御) 経由。素材として repo にある Yoshida/Mackey transfer 基盤が使える見込み。
⚠ `A ⊆ Z_{p−1}(P)` 枝は不要なので、`p` 奇 + `A` abelian の枝だけを狙う。
着手時に (a) Gorenstein §7.6 (証明は M. Hall 参照で本書に無し)、(b) Isaacs Ch.5/10
の focal subgroup / Grün 周辺、(c) Coq odd-order の対応物の有無を実測してから
方針を確定する ([[feedback-ask-chatgpt-for-elided-gaps]] も選択肢)。

## 完了条件

- 上記主定理が sorry-free で landing、AxiomsCheck 登録
- Pf II (17) が `G/O³(G) ≅ R₂⟨s⟩/O³(R₂⟨s⟩)` 相当を実際に消費できる

## 参照

- issues/2053-pf-suzuki-theorem-b.md (消費点、(17) の全論法)
- references/peterfalvi/pdf/05.4_pp_108_114_The_First_Case.pdf p. 108 (statement) / p. 114 (使用)
- OddOrder/Isaacs/Ch10_MoreTransfer/Yoshida.lean (class < p 版、既存)
- OddOrder/Peterfalvi/Appendices/Suzuki/FirstCase/StepTwelveTransfer.lean (既存版の消費例)
