/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# BG §1: Elementary Properties of Solvable Groups

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
Chapter I §1 (pp. 1-8), mmd `references/bg/local-analysis.mmd` L310-585, **22 結果** (Lemma/
Proposition/Theorem/Corollary 1.1-1.22).

## 構造 (BG §1 全 22 結果)

§1 を概念別に 7 つの sub-section に整理:

- **§1A** Solvable group basics (Lem 1.1, Prop 1.2-1.4)
- **§1B** A-invariant Hall theory (Prop 1.5, Prop 1.6) — Peterfalvi で多数引用
- **§1C** Frattini + Burnside operator (Lem 1.7, Thm 1.8, Lem 1.9, Prop 1.10)
- **§1D** p-odd action (Thm 1.11, Cor 1.12, Thm 1.13 Thompson critical)
- **§1E** Sylow lift + Hall-Higman + noncyclic auto (Lem 1.14, Prop 1.15, Prop 1.16)
- **§1F** Focal + Burnside + Maschke (Thm 1.17, Thm 1.18, Cor 1.19, Thm 1.20) — **mathlib 直接**
- **§1G** p-length one + p-group normal series (Lem 1.21, Lem 1.22)

## Isaacs FGT / mathlib 対応表

CLAUDE.md no-mathlib-wrapper policy 準拠: mathlib 直接対応がある §1F の 4 結果は
**section docstring 記載のみで個別 theorem を書かない**. BG 番号 ↔ Isaacs ↔ mathlib の
対応関係を以下に明記.

| BG | Isaacs FGT | mathlib | 本ファイル |
|---|---|---|---|
| **Thm 1.8** (Burnside operator) | Thm 1.8 | (Ch.1 §1B TODO) | ❌ Phase 1 待ち |
| **Thm 1.11** (p odd + Ω₁ fixed) | Thm 4.36 | Phase 1 Ch.4 §4D (進行中) | ❌ Phase 1 待ち |
| **Thm 1.13** (Thompson critical) | (Ch.4 endgame or Ch.7) | (Phase 1 未) | ❌ Phase 1 待ち |
| **Lem 1.14** (quotient Sylow lift) | — | `Sylow.exists_comap_subtype_eq` (mathlib) | ⏳ 次 commit 予定 |
| **Prop 1.15(a)** (Hall-Higman 1.2.3) | Thm 3.21 | Phase 1 `hall_higman_1_2_3` ✅ | ⏳ 次 commit 予定 (thin wrap) |
| **Thm 1.17** (Focal Subgroup) | Thm 5.21 | `Subgroup.commutator_inf_eq_focalSubgroup` ✅ | ✅ no-wrapper, see Phase 1 Ch.5 `abelian_sylow_commutator_inf_eq_focal` |
| **Thm 1.18** (Burnside p-comp) | Thm 5.13 | `MonoidHom.ker_transferSylow_isComplement'` ✅ | ✅ no-wrapper, mathlib 直接利用 |
| **Cor 1.19(b)** (Z-group ⇒ G' Hall) | — | `IsZGroup.coprime_commutator_index` ✅ | ✅ no-wrapper, mathlib `SpecificGroups/ZGroup.lean:280` 直接 |
| **Thm 1.20** (Maschke) | — | `Maschke` (mathlib `RepresentationTheory/Maschke.lean`) ✅ | ✅ no-wrapper, mathlib 直接 |
| **Lem 1.22** (∃ normal of each p-power order) | (Ch.1 系の standard) | `IsPGroup.normal_inf_center_nontrivial` (Phase 1 ✅) + Cauchy + induction | ✅ **本ファイルで実装** |

## 形式化進捗 (2026-05-23 着手)

- **§1F mathlib 対応** (Thm 1.17-1.20): docstring 完了
- **§1G Lem 1.22**: 実装 (本ファイル)
- **§1G Lem 1.21** (p-length one): 別ファイル `PLength.lean` (将来)
- **§1A-§1E**: Phase 1 完成度 + shared module (`MinimalNormal`, `InvariantSubgroup`,
  `ChiefSeries`, `FrattiniPGroup`) 待ち

## Audit context

Phase 2a 第 1 波 audit (2026-05-23) で §1 を 4 視点で再調査済.
詳細: `notes/bg/s01_solvable.md` + `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`.

主要 audit 発見 (§1 関連):
- Lem 1.1 "43+ 回引用" → 実測 0 in §2+ (Peterfalvi `[Is] Lem 1.5` Schur と混同推定)
- Prop 1.2 "22 回引用" → 実測 6
- Thm 1.13 ↔ Isaacs 4.31 同一視 → 別物 (Thompson critical ≠ Thompson P×Q)
- Cor 1.19(b) → mathlib `IsZGroup.coprime_commutator_index` 直接ヒット
- 内部 hub は **Prop 1.5(d)** (6 §1 proofs)
-/

namespace OddOrder.BG.Ch1.S01

/-! ## §1A: Solvable group basics (Lem 1.1, Prop 1.2-1.4) — 未実装

Phase 1 Ch.3 (Hall) + shared module `MinimalNormal.lean`, `ChiefSeries.lean` 待ち. -/

/-! ## §1B: A-invariant Hall theory (Prop 1.5, Prop 1.6) — 未実装

shared module `InvariantSubgroup.lean` + Phase 1 Ch.3 + Ch.4 §4D 待ち. **Peterfalvi で
最多引用** (Prop 1.5: 25 cites, Prop 1.6: 13 cites). -/

/-! ## §1C: Frattini + Burnside operator (Lem 1.7-1.9, Prop 1.10) — 未実装

mathlib `frattini` + shared `FrattiniPGroup.lean` (1.7(b)(d)) + Phase 1 Ch.1 §1B
(Thm 1.8) 待ち. -/

/-! ## §1D: p-odd action (Thm 1.11-1.13) — 未実装

Phase 1 Ch.4 §4D Thm 4.36 (Thm 1.11) + Thompson critical (Thm 1.13) 待ち. `OmegaSubgroup.lean`
✅ 完成済. -/

/-! ## §1E: Sylow lift + Hall-Higman + noncyclic auto (Lem 1.14, Prop 1.15, Prop 1.16)

Lem 1.14 (Sylow lift): mathlib `Sylow.exists_comap_subtype_eq` 直接利用予定 — 次 commit.
Prop 1.15(a) (Hall-Higman 1.2.3): Phase 1 ✅ `hall_higman_1_2_3` thin wrap 予定 — 次 commit.
Prop 1.16: 新規 helper `exists_two_subgroups_index_p_of_noncyclic` 要. -/

/-! ## §1F: Focal + Burnside + Maschke (Thm 1.17-1.20) — **mathlib 直接, no-wrapper**

CLAUDE.md no-mathlib-wrapper policy により 4 結果とも個別 theorem は書かない.
利用箇所では mathlib (or Phase 1 Ch.5) の名前を直接呼ぶ.

- **BG Thm 1.17** (Focal Subgroup) ≡ Isaacs Thm 5.21 ≡ mathlib
  `Subgroup.commutator_inf_eq_focalSubgroup`. Phase 1 wrapper:
  `OddOrder.Isaacs.Ch05.abelian_sylow_commutator_inf_eq_focal`.
- **BG Thm 1.18** (Burnside p-complement) ≡ Isaacs Thm 5.13 ≡ mathlib
  `MonoidHom.ker_transferSylow_isComplement'` (`Mathlib/GroupTheory/Transfer.lean:275`).
- **BG Cor 1.19(a)** (cyclic Sylow ⇒ S ∩ G' = 1 or S ⊆ G'):
  Phase 1 Ch.5 `IsCyclic.isComplement'` 周辺で間接実現. **Cor 1.19(b)** (Z-group ⇒ G'
  Hall): mathlib `IsZGroup.coprime_commutator_index`
  (`Mathlib/GroupTheory/SpecificGroups/ZGroup.lean:280`) 直接.
- **BG Thm 1.20** (Maschke): mathlib `Mathlib/RepresentationTheory/Maschke.lean`.

主結果のため Lean 上では Phase 1 / mathlib を直接 import + 利用すれば足り,
BG §1 docstring がトレーサビリティを担保. -/

/-! ## §1G: p-length one + p-group normal series (Lem 1.21, Lem 1.22)

- **Lem 1.21** (p-length one の 5 性質): BG-unique def, 別ファイル `PLength.lean` (将来).
- **Lem 1.22** (p-group N ⊴ G, |N|=p^k ⇒ ∀ r ≤ k, ∃ L ⊴ G, L ≤ N, |L|=p ^ r):
  本ファイル下記で実装.

### Lem 1.22 implementation -/

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- **BG Lemma 1.22**: in a finite `p`-group `G`, every normal subgroup `N` of order `p^k`
contains, for each `0 ≤ r ≤ k`, a normal subgroup of `G` of order `p ^ r`.

**Proof** (BG p.8): strong induction on `|G|`. Base: `N = ⊥` or `r = 0` trivial. Step:
`r ≥ 1`, so `N ≠ 1` ⇒ `N ⊓ Z(G) ≠ 1` (Phase 1 `IsPGroup.normal_inf_center_nontrivial`).
Take `Z ≤ N ⊓ Z(G)` of order `p` (Cauchy). `Z` is central ⇒ normal in `G`. By IH on `G/Z`
(strictly smaller), `N/Z` contains normal subgroup `L̅/Z` of order `p^{r-1}`. The preimage
`L` in `G` satisfies `|L| = p ^ r`, `L ≤ N`, `L ⊴ G`. -/
theorem normal_subgroup_card_pow_le_of_pGroup
    (hG : IsPGroup p G) {N : Subgroup G} [N.Normal] {r : ℕ}
    (hr_dvd : p ^ r ∣ Nat.card N) :
    ∃ L : Subgroup G, L.Normal ∧ L ≤ N ∧ Nat.card L = p ^ r := by
  sorry

end OddOrder.BG.Ch1.S01
