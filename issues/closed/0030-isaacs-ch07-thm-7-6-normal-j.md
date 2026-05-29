---
id: 30
slug: isaacs-ch07-thm-7-6-normal-j
title: "Isaacs Thm 7.6 normal-J theorem (= BG Thm 6.2 odd-order) - FT critical"
created: 2026-05-26
---

# Isaacs Thm 7.6 normal-J theorem (= BG Thm 6.2 odd-order) - FT critical

## 背景

**Isaacs Thm 7.6** (mmd L3832) normal-J theorem:

> (i) G p-solvable, (ii) p ≠ 2, (iii) Sylow-2 abelian, (iv) O_{p'}(G) = 1,
> (v) P = C_G(Z(P)) ⇒ J(P) ⊴ G.

**= BG Theorem 6.2 odd-order 等価版**. **FT クリティカル度 HIGHEST**: BG §6, §8, §9,
App.A で 7 ヶ所超で直接引用 (L2456, L2480, L2482, L2511, L2515, L5014, L5032).

## やること

- [ ] Resolve Thm 7.5 first (issue #29).
- [ ] Confirm Ch.4 Thm 4.35 (Ω₁ fixed) is available.
- [ ] Confirm Ch.6 Thm 6.20 (abelian coprime ⟨C_N(a)⟩=N) is available.
- [ ] Confirm Hall-Higman Ch.3 Thm 3.21 is available.
- [ ] Implement 8-step proof (mmd L3832-L3896):
  1. Minimum counterexample G with J(P) not normal.
  2. O_{p'}(G) = 1 (by hypothesis).
  3. V := Z(J(P)). Abelian and characteristic in P.
  4. Apply Ch.6 Thm 6.20: action of G on V via P-conjugation.
  5. Apply Ch.4 Thm 4.35 to find P-invariant element.
  6. Apply Hall-Higman 3.21 to control rank.
  7. Apply Thm 7.5 (normal-P) in subquotient.
  8. Conclude J(P) ⊴ G.
- [ ] Add top-level theorem `OddOrder.Isaacs.Ch07.normal_J_*`.

## 2026-05-26 update — sub-agent investigation 結果

- **Cor 4.35** は `OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p` で
  sorry-free 提供済み (`Ch04_Commutators/Main.lean:3437`).  Step 6 hypothesis 直接適合.
- **§7B (Main.lean:2463-2482) は docstring placeholder のみ, bridge ゼロ**.
- 8-step proof は §7A 流の 1100+ LOC bridge accumulation 相当を必要とする:
  - Step 1: Hall-Higman 3.21 3 bridges (`Z(P) ≤ U`, `O_{p'}(H)=1`, `C_{G/U}(L/U) ≤ L/U`)
  - Step 2: J(P) char-in-P + characteristic-through-normal 強化
  - Step 3-4: Subgroup `H = LA`, Sylow-p of H, induction + conjugation commutator
  - Step 5: 6.20 adapter
  - Step 6: 4.35 adapter + Ω₁(Z(U)) def (Ch.7 ch07_thompson.md L507 design open)
  - Step 7: |VD| ≤ |A| from A ∈ E(P) maximality
  - Step 8: Thm 7.5 direct application
- **推定**: ~800-1500 LOC of new bridges, **multi-session work** even after 7.5 lands.
- 着手順案: Step 1 (Hall-Higman corollaries) → Ω₁ design → Step 5/6/8 (existing Ch.4/Ch.6/7.5 adapters).
- 候補識別子: `thompsonJ_normal_of_centralizer_center_eq_of_oPiCoreCompl_eq_bot` (long form)
  または `thompsonJ_normal_of_self_centralizing` (short).  `^theorem normal_J…` 規則を
  満たすには `normal_J_of_self_centralizing` 等にリネーム.

## 完了条件

- Top-level theorem matching goal-grep `^theorem normal_J…`.
- Proof sorry/axiom-free.
- `lake build OddOrder` green.
- AxiomsCheck passes for this flagship theorem.

## 参照

- `notes/isaacs/ch07_thompson.md` — section §7B
- `references/isaacs/finite-group-theory.mmd` L3832-L3896
- BG §App.A Thm A.4(b) — equivalent statement
- Issue #29 (Thm 7.5 — prerequisite)
- `OddOrder.GroupTheory.ThompsonSubgroup` — `J(P)` def

## 完了確認 (2026-05-29) — CLOSED

top-level theorem **`OddOrder.Isaacs.Ch07.normal_J`** (`S7B2_NormalJ_PComplement.lean:1416`) が
完成済を確認:

- 署名 = reduced Thm 7.6 (P Sylow p, p≠2, p-separable, 2-subgroups abelian, **O_{p'}(G)=⊥**,
  **P=C_G(Z(P))** ⇒ `J(P).Normal`)。これは issue statement の (i)-(v) と完全一致。
- 委譲先 **`thompsonJ_le_opCore_of_normal_J_hypotheses`** (`S7B2:1299`) = `Nat.card G` 強帰納の
  **本物の証明** (forward 仮説スキャフォールドではない; 仮説は全て正当な reduced-case 条件で
  hoisted hard content ではない。`scaffold-sorry-free-not-done` 検証クリア)。
- S7B2 は **sorry 0**、`lake build OddOrder` green、**AxiomsCheck 登録済** (`AxiomsCheck.lean:499`)。

⚠ **2026-05-26 update の「8-step bridge ゼロ・~800-1500 LOC multi-session」は stale** —
その後 `thompsonJ_le_opCore_of_normal_J_hypotheses` (強帰納) として完成した。

★ これは **reduced case** (O_{p'}=⊥, P=C_G(Z(P)))。**BG Thm 6.2 一般形** (`Z(J(S))·O_{p'}◁G`,
任意 S) は別系統 = App.A→App.B 連鎖 (issue 0047✅ A.4, 0049 A.5, App.B Puig L(S))。

完了条件すべて充足。クローズ。
