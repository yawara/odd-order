---
id: 6
slug: isaacs-3e-coprime-action-tier-2
title: "Isaacs §3E Coprime action Tier 2 (Thm 3.26 / 3.31-3.34) 実装"
created: 2026-05-24
---

# Isaacs §3E Coprime action Tier 2 (Thm 3.26 / 3.31-3.34) 実装

## 背景

Isaacs §3E (Coprime action, pp.96-104) の Tier 1 は
[`OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean`](../OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean)
に既に 9 件 sorry-free 完成 (Lem 3.24 Glauberman, Thm 3.23(a)(b), Cor 3.25, Thm 3.27,
Cor 3.28, Cor 3.29, Cor 3.30 + helpers). AxiomsCheck flagship 入り.

**未実装の Tier 2** (本 issue):

| Isaacs # | 内容 |
|---|---|
| Thm 3.26 | A-invariant 共役類 ↔ `C_G(A)` の共役類 (bijection) |
| Thm 3.31 Hartley-Turull | 軌道構造が abelian H に転送可 |
| Thm 3.32 | P A-invariant Sylow ⇒ `P ∩ C ∈ Syl_p(C)` (C = C_G(A)) |
| Thm 3.33 | fixed point 数一致 ⇒ orbit-preserving bijection |
| Thm 3.34 | A-orbit sizes m, n coprime ⇒ size mn の orbit も存在 |

Tier 2 は **Ch.4 §4C-§4D (`[G, A]` 構造 + coprime action machinery)** 完成を前提とする.
具体的には Three-Subgroup Lemma + Cor 3.28 ([G,A] = [G,A,A] 型の reduction) を要する.

Hartley-Turull (Thm 3.31) は Isaacs 独自結果で BG/Peterfalvi 直接引用 0 件
([notes/isaacs/ch03_split.md](../notes/isaacs/ch03_split.md) §3E 参照).
Phase 1 完成度のためには実装するが, FT 経路としての critical 度は低い.

## やること

- [ ] Ch.4 §4C-§4D の coprime action machinery (`[G, A]` 構造, Three-Subgroup Lemma 等) 完成を待つ
- [ ] `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean` に Tier 2 セクションを追加
- [ ] Thm 3.26 bijection (A-inv conj class ↔ C_G(A) conj class) 実装
- [ ] Thm 3.31 Hartley-Turull 実装
- [ ] Thm 3.32 `P ∩ C ∈ Syl_p(C)` 実装
- [ ] Thm 3.33 fixed point counting 実装
- [ ] Thm 3.34 A-orbit size mn 実装

## 完了条件

- `Ch04_Commutators/ForwardFromCh03.lean` に Tier 2 全 5 件が sorry-free theorem として実装される
- `lake build OddOrder.AxiomsCheck` 通過

## 参照

- [OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean](../OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean) (Tier 1 完成済)
- [notes/isaacs/ch03_split.md](../notes/isaacs/ch03_split.md) §3E
- [notes/isaacs/ch04_commutators.md](../notes/isaacs/ch04_commutators.md) §4C-§4D
- [notes/meta/ch04_07_audit_2026_05_22.md](../notes/meta/ch04_07_audit_2026_05_22.md)
- Isaacs FGT pp.96-104 (§3E)

> 🧾 (2026-07-02 hub 全体レビュー): 前提の Ch.4 §4C/§4D は **完備** (Ch04 Main.lean §4C/§4D = 完成) — ただし本 issue は off-FT-path につき coverage phase まで park 継続。
