/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7D1_BurnsideSetup

/-!
# Basic

Prefix-split from `OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# OddOrder.Isaacs.Ch07 — The Thompson Subgroup

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 7 (pp. 201-222) の Lean 化.

**FT クリティカル経路の頂点**. **章本体は 8 結果**だが BG/Peterfalvi 経由で
Feit-Thompson 局所解析の中核を担う:

- **Thm 7.1 Thompson normal p-complement** — Ch.6 Thm 6.23 を完備化.
- **Thm 7.2** — `J(P)` は Q 内 characteristic (本ファイルで `thompsonJ_eq_of_le_of_le`
  経由で完成済).
- **Lem 7.3 GL(2,p) 補題** — Thm 7.5 の道具.
- **Lem 7.4 SL(2,q) 唯一 involution = -I** — Thm 7.3 の道具.
- **Thm 7.5 normal-P theorem** — Thm 7.6 の中核 step.
- **Thm 7.6 normal-J theorem** ≡ BG Thm 6.2 (odd-order 仮定). **FT クリティカル度
  HIGHEST**. BG §6, §8, §9, App.A で 7 ヶ所超で直接引用.
- **Lem 7.7** — `N/C` 系の `p'`-quotient (Lem 2.17 拡張).
- **Thm 7.8 Burnside `p^a q^b`** — character-free 証明 (Goldschmidt-Bender-Matsuyama).

## Notes / Roadmap

詳細な mini-roadmap は [`notes/isaacs/ch07_thompson.md`](../../../notes/isaacs/ch07_thompson.md)
参照. 主要な设计判断 (HasNormalPComplement def, `Aut(E) ≅ GL(n,p)` 橋渡し,
`p`-stability 概念) も同ノートに集約.

## Shared modules

* [`OddOrder.GroupTheory.ElementaryAbelian`](../../GroupTheory/ElementaryAbelian.lean) —
  `IsElementaryAbelian p G` / `Subgroup.IsElementaryAbelian H p` def (Ch.3, Ch.6, Ch.7 共用).
* [`OddOrder.GroupTheory.ThompsonSubgroup`](../../GroupTheory/ThompsonSubgroup.lean) —
  `Subgroup.thompsonJ P p` def + Thm 7.2 (BG App.A, App.B 共用視野).

## Implementation order (本ファイル内)

1. ✅ Thm 7.2 (`thompsonJ` shared module 経由)
2. ✅ Lem 7.4 SL(2,q) — 独立小テーマ (先行章不要)
3. ✅ Lem 7.7 — Lem 2.17 拡張 (Ch.2 完成済から短い延長)
4. ✅ Lem 7.3 GL(2,p) 補題 — `|L|`-induction + Lem 7.4 + Ch.4 coprime action
5. Thm 7.5 normal-P → Thm 7.6 normal-J
6. (Ch.5 §5E 5.26 完成後) Thm 7.1
7. (上記完成後) Thm 7.8 Burnside

未着手 statement の def 系前提 (`HasNormalPComplement`, `GeneralLinearGroup` 引数法,
`Aut(E) ≅ GL(n,p)`) は実装時に決める.

## File layout (split per issue 0038)

Dependency-ordered split to keep the build inner-loop fast (issue 0038).
Import chain: S7A1 → S7A2 → S7B1 → S7B2 → S7C →
S7C Sylow maximal → S7C centralizer center → S7C abelian quotient complement →
S7C Thompson p-complement final → S7D1 → Main.

* `S7A1_JpGL2p` — §7A part 1 (J(P), Thm 7.1 stmt, Lem 7.3 GL(2,p))
* `S7A2_NormalPThm75` — §7A part 2 (Lem 7.3 formal, Thm 7.5, action infra)
* `S7B1_NormalJ` — §7B Steps 1-6
* `S7B2_NormalJ_PComplement` — §7B close + §7C infrastructure (Lem 7.7)
* `S7C_ThompsonPComplement` — §7C quotient identifications + Thm 7.1 assembly
* `S7C_SylowMaximal` — §7C Thm 7.1 Step 4 (Sylow subgroup maximality)
* `S7C_CentralizerCenter` — §7C Thm 7.1 Step 5 (`C_G(Z(P)) = P`)
* `S7C_AbelianQuotientComplement` — §7C Thm 7.1 Step 6 (abelian Sylow `2`-subgroups)
* `S7C_ThompsonPComplementFinal` — §7C Thm 7.1 Step 7 and final strong-induction assembly
* `S7D1_BurnsideSetup` — §7D setup (Thm 7.8 stmt, scaffolding, Steps 2-9 decomp)
* `Main` (this file) — §7D Step 3, Step 8, Step 9, final assembly
-/

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise
open scoped IsMulCommutative -- rc2: IsMulCommutative→CommGroup/Monoid now scoped

variable {G : Type*} [Group G]

/-! ### §7D Step 3 — *not both cores nontrivial* (Isaacs L3982-3993)

The asymmetric core `step3_main` does the full construction once (`Z = Z_p Z_q`
abelian normal, `M = N_G(Z)` unique maximal by Step 1, `S ∈ Syl_p(M)` not full,
the `N_P(S) > S` conjugation `g ∈ G - M` with `S^g = S`, `A = Z_p^g`), then
splits on whether `A` acts faithfully on `Z_q`:
- not faithful (or non-cyclic): `Z_q = ⟨C_{Z_q}(a)⟩ ⊆ M^g`, `Z_p ⊆ M^g`, so
  `Z ⊆ M^g`, forcing `M = M^g`, `g ∈ M` — contradiction;
- faithful: `A` (nontrivial `p`-group) acts faithfully on the cyclic `Z_q`, so
  `p ∣ q-1`, i.e. `p < q`.

It returns `IsCyclic Z_p ∧ (IsCyclic Z_q → p < q)`.  `step3_not_both_opCore_ne_bot`
applies it with `(p,q)` and `(q,p)` (same `M`): `Z_p, Z_q` cyclic and `p < q`,
`q < p` — contradiction. -/


/-- **§7D Step 3 arithmetic** — a nontrivial `p`-group `A` acting faithfully on a
cyclic `q`-group `C` (via an injective `A →* MulAut C`) forces `p < q`.

`A` injects into `MulAut C ≅ (ZMod q^j)ˣ`, which has order `φ(q^j) = q^{j-1}(q-1)`
(`IsCyclic.card_mulAut`).  Since `p ≠ q`, `p ∤ q^{j-1}`, so `p ∣ q-1`, giving
`p ≤ q-1 < q`. -/
private theorem prime_lt_of_pGroup_faithful_on_cyclic
    {A C : Type*} [Group A] [Finite A] [Group C] [Finite C] [IsCyclic C]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hA : IsPGroup p A) (hA_nt : Nontrivial A)
    (hC : IsPGroup q C) (hpq : p ≠ q)
    (φ : A →* MulAut C) (hφ : Function.Injective φ) :
    p < q := by
  classical
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  -- `p ∣ |A|`  (`|A| = p^m`, `m ≥ 1` since `A` nontrivial).
  obtain ⟨m, hmA⟩ := (IsPGroup.iff_card (p := p) (G := A)).mp hA
  have hA1 : 1 < Nat.card A := Finite.one_lt_card_iff_nontrivial.mpr hA_nt
  have hm0 : m ≠ 0 := by rintro rfl; rw [pow_zero] at hmA; omega
  have hpA : p ∣ Nat.card A := hmA ▸ dvd_pow_self p hm0
  -- `|A| ∣ |MulAut C|`  (`φ` injective ⇒ `A ≃* range ≤ MulAut C`).
  have hrange : Nat.card A ∣ Nat.card (MulAut C) := Subgroup.card_dvd_of_injective φ hφ
  -- `|MulAut C| = φ(|C|)`, `|C| = q^j`.
  obtain ⟨j, hjC⟩ := (IsPGroup.iff_card (p := q) (G := C)).mp hC
  have hp_tot : p ∣ Nat.totient (q ^ j) := by
    have := hpA.trans hrange
    rwa [IsCyclic.card_mulAut, hjC] at this
  -- `j ≥ 1` (else `φ(1) = 1`, `p ∤ 1`).
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, pow_zero, Nat.totient_one] at hp_tot
      exact absurd (Nat.le_of_dvd one_pos hp_tot) (by have := hp.two_le; omega)
    · exact h
  rw [Nat.totient_prime_pow hq hj0] at hp_tot
  -- `p ∣ q^{j-1}(q-1)`, `p ∤ q^{j-1}` ⇒ `p ∣ q-1`.
  have hp_not_qpow : ¬ p ∣ q ^ (j - 1) := fun hdvd =>
    hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))
  have hp_q1 : p ∣ (q - 1) := ((Nat.Prime.dvd_mul hp).mp hp_tot).resolve_left hp_not_qpow
  have := Nat.le_of_dvd (by have := hq.two_le; omega) hp_q1
  have := hq.two_le
  omega

/-- `Z(O_p(M))` viewed in `H` (for a subgroup `M ≤ H`): the image of
`zCenterOpCoreSubgroup ↥M p` under `M.subtype`. -/
private def zCenterOpCoreH {H : Type*} [Group H] (M : Subgroup H) (p : ℕ) : Subgroup H :=
  (zCenterOpCoreSubgroup ↥M p).map M.subtype

open OddOrder.Isaacs.Ch06 in
/-- **§7D Step 3 core** — the asymmetric construction; see the section docstring. -/
theorem step3_main
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_max : IsCoatom M)
    (hOp : OddOrder.Isaacs.Ch01.opCore p ↥M ≠ ⊥)
    (hOq : OddOrder.Isaacs.Ch01.opCore q ↥M ≠ ⊥) :
    IsCyclic ↥(zCenterOpCoreH M p) ∧
      (IsCyclic ↥(zCenterOpCoreH M q) → p < q) := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  haveI : Nontrivial ↥M := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hMbot
    apply hOp
    have : Subsingleton ↥M := by rw [hMbot]; infer_instance
    exact Subgroup.eq_bot_of_subsingleton _
  have hM_ne_top : M ≠ ⊤ := hM_max.1
  -- `Z_p = Z(O_p(M))`, `Z_q = Z(O_q(M))` as subgroups of `↥M`.
  set Zp : Subgroup ↥M := zCenterOpCoreSubgroup ↥M p with hZp_def
  set Zq : Subgroup ↥M := zCenterOpCoreSubgroup ↥M q with hZq_def
  -- their `H`-images.
  set ZpH : Subgroup H := zCenterOpCoreH M p with hZpH_def
  set ZqH : Subgroup H := zCenterOpCoreH M q with hZqH_def
  have hZpH_eq : ZpH = Zp.map M.subtype := rfl
  have hZqH_eq : ZqH = Zq.map M.subtype := rfl
  -- `Z_p, Z_q` nontrivial (nontrivial p-/q-group has nontrivial center).
  have hZp_ne_bot : Zp ≠ ⊥ := by
    rw [hZp_def, zCenterOpCoreSubgroup, Ne, Subgroup.map_eq_bot_iff_of_injective _
      (OddOrder.Isaacs.Ch01.opCore p ↥M).subtype_injective]
    haveI : Nontrivial ↥(OddOrder.Isaacs.Ch01.opCore p ↥M) :=
      (OddOrder.Isaacs.Ch01.opCore p ↥M).nontrivial_iff_ne_bot.mpr hOp
    exact (Subgroup.center _).nontrivial_iff_ne_bot.mp
      (OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥M).center_nontrivial
  have hZq_ne_bot : Zq ≠ ⊥ := by
    rw [hZq_def, zCenterOpCoreSubgroup, Ne, Subgroup.map_eq_bot_iff_of_injective _
      (OddOrder.Isaacs.Ch01.opCore q ↥M).subtype_injective]
    haveI : Nontrivial ↥(OddOrder.Isaacs.Ch01.opCore q ↥M) :=
      (OddOrder.Isaacs.Ch01.opCore q ↥M).nontrivial_iff_ne_bot.mpr hOq
    exact (Subgroup.center _).nontrivial_iff_ne_bot.mp
      (OddOrder.Isaacs.Ch01.opCore_isPGroup q ↥M).center_nontrivial
  -- `ZpH, ZqH` nontrivial, `p`-/`q`-groups.
  have hZpH_ne_bot : ZpH ≠ ⊥ := by
    rw [hZpH_eq, Ne, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]; exact hZp_ne_bot
  have hZqH_ne_bot : ZqH ≠ ⊥ := by
    rw [hZqH_eq, Ne, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]; exact hZq_ne_bot
  have hZpH_pgroup : IsPGroup p ZpH := by
    rw [hZpH_eq]; exact (zCenterOpCoreSubgroup_isPGroup p).map M.subtype
  have hZqH_qgroup : IsPGroup q ZqH := by
    rw [hZqH_eq]; exact (zCenterOpCoreSubgroup_isPGroup q).map M.subtype
  -- `Z_p ⊴ M`, `Z_q ⊴ M` (the centers of the cores are `M`-normal).
  haveI hZp_normal : Zp.Normal := by rw [hZp_def]; exact zCenterOpCoreSubgroup_normal
  haveI hZq_normal : Zq.Normal := by rw [hZq_def]; exact zCenterOpCoreSubgroup_normal
  -- L1. `Z := Z_p · Z_q ≤ M`, nontrivial (Isaacs L3983).
  have hZpH_le_M : ZpH ≤ M := by rw [hZpH_eq]; exact Subgroup.map_subtype_le _
  have hZqH_le_M : ZqH ≤ M := by rw [hZqH_eq]; exact Subgroup.map_subtype_le _
  set Z : Subgroup H := ZpH ⊔ ZqH with hZ_def
  have hZpH_le_Z : ZpH ≤ Z := le_sup_left
  have hZqH_le_Z : ZqH ≤ Z := le_sup_right
  have hZ_le_M : Z ≤ M := sup_le hZpH_le_M hZqH_le_M
  have hZ_ne_bot : Z ≠ ⊥ := by
    intro h; exact hZpH_ne_bot (le_bot_iff.mp (h ▸ hZpH_le_Z))
  -- `p, q ∣ |Z|` (nontrivial `p`-/`q`-subgroups `ZpH, ZqH ≤ Z`).
  have hp_dvd_Z : p ∣ Nat.card ↥Z := by
    haveI : Nontrivial ↥ZpH := ZpH.nontrivial_iff_ne_bot.mpr hZpH_ne_bot
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥ZpH)).mp hZpH_pgroup
    have hn0 : n ≠ 0 := by
      rintro rfl; rw [pow_zero] at hn
      exact absurd hn (Finite.one_lt_card_iff_nontrivial.mpr ‹_›).ne'
    exact (hn ▸ dvd_pow_self p hn0).trans (Subgroup.card_dvd_of_le hZpH_le_Z)
  have hq_dvd_Z : q ∣ Nat.card ↥Z := by
    haveI : Nontrivial ↥ZqH := ZqH.nontrivial_iff_ne_bot.mpr hZqH_ne_bot
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q) (G := ↥ZqH)).mp hZqH_qgroup
    have hn0 : n ≠ 0 := by
      rintro rfl; rw [pow_zero] at hn
      exact absurd hn (Finite.one_lt_card_iff_nontrivial.mpr ‹_›).ne'
    exact (hn ▸ dvd_pow_self q hn0).trans (Subgroup.card_dvd_of_le hZqH_le_Z)
  -- `M ≤ N_H(Z)` (`Z_p, Z_q` are `M`-normal, so `M` normalizes their join).
  have hM_norm_ZpH : M ≤ Subgroup.normalizer ZpH := by
    have h := map_le_normalizer_map_of_normal (φ := M.subtype) (P := ⊤) (L := Zp)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    rwa [← hZpH_eq] at h
  have hM_norm_ZqH : M ≤ Subgroup.normalizer ZqH := by
    have h := map_le_normalizer_map_of_normal (φ := M.subtype) (P := ⊤) (L := Zq)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    rwa [← hZqH_eq] at h
  have hM_norm_Z : M ≤ Subgroup.normalizer Z :=
    (le_inf hM_norm_ZpH hM_norm_ZqH).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup ZpH ZqH)
  -- `Z` is abelian (centers of `O_p,O_q` are commutative and commute), hence nilpotent.
  haveI hZp_comm : IsMulCommutative Zp := by
    rw [hZp_def]; unfold zCenterOpCoreSubgroup; infer_instance
  haveI hZq_comm : IsMulCommutative Zq := by
    rw [hZq_def]; unfold zCenterOpCoreSubgroup; infer_instance
  haveI hZpH_comm : IsMulCommutative ZpH := by rw [hZpH_eq]; infer_instance
  haveI hZqH_comm : IsMulCommutative ZqH := by rw [hZqH_eq]; infer_instance
  have hdisjM : Disjoint Zp Zq :=
    IsPGroup.disjoint_of_ne p q hpq Zp Zq
      (zCenterOpCoreSubgroup_isPGroup p) (zCenterOpCoreSubgroup_isPGroup q)
  have hcross : ∀ a ∈ ZpH, ∀ b ∈ ZqH, Commute a b := by
    intro a ha b hb
    rw [hZpH_eq, Subgroup.mem_map] at ha
    rw [hZqH_eq, Subgroup.mem_map] at hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact (Subgroup.commute_of_normal_of_disjoint Zp Zq hZp_normal hZq_normal hdisjM
      x y hx hy).map M.subtype
  have hZ_le_cent : Z ≤ Subgroup.centralizer (Z : Set H) := by
    rw [hZ_def,
      show (↑(ZpH ⊔ ZqH) : Set H) = ↑(Subgroup.closure (↑ZpH ∪ ↑ZqH : Set H)) by
        rw [Subgroup.sup_eq_closure],
      Subgroup.centralizer_closure, Subgroup.sup_eq_closure, Subgroup.closure_le]
    rintro g (hg | hg) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
      rintro h (hh | hh)
    · exact setLike_mul_comm (s := ZpH) hh hg
    · exact (hcross g hg h hh).symm
    · exact hcross h hh g hg
    · exact setLike_mul_comm (s := ZqH) hh hg
  haveI hZ_comm : IsMulCommutative Z :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp hZ_le_cent
  haveI hZ_nilp : Group.IsNilpotent ↥Z := inferInstance
  -- L2. `M = N_H(Z)`, and `M` is the unique maximal subgroup containing `Z` (Step 1).
  have hNZ_eq_M : Subgroup.normalizer Z = M :=
    maximal_eq_normalizer_of_M_normalizes hM_max hZ_ne_bot hZ_le_M hM_norm_Z
  have hcoatom : IsCoatom (Subgroup.normalizer (Z : Set H)) := by rw [hNZ_eq_M]; exact hM_max
  have hZ_unique : ∀ X : Subgroup H, IsCoatom X → Z ≤ X → X = M := fun X hX hZX =>
    (step1_unique_maximal_containing_nilpotent hpq hH_card hSubgroupsSolvable
      hZ_nilp hp_dvd_Z hq_dvd_Z hcoatom hX hZX).trans hNZ_eq_M
  -- L3. `Z(H) = ⊥` (else `H` abelian ⇒ `M` proper nontrivial normal, contra simplicity),
  -- hence `1 ≠ z ∈ Z ⇒ C_H(z) < H`, contained in a maximal ⊇ Z, which is `M`.
  have hcenter_bot : Subgroup.center H = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) inferInstance
      with h | h
    · exact h
    · exfalso
      have hMnorm : M.Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hg : g * n = n * g := (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top g) n).symm
        rw [hg, mul_inv_cancel_right]; exact hn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M hMnorm with hM | hM
      · exact absurd hM (M.nontrivial_iff_ne_bot.mp inferInstance)
      · exact hM_max.1 hM
  have hL3 : ∀ z ∈ Z, z ≠ 1 → Subgroup.centralizer ({z} : Set H) ≤ M := by
    intro z hz hz1
    have hZ_le_Cz : Z ≤ Subgroup.centralizer ({z} : Set H) :=
      hZ_le_cent.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz))
    have hCz_ne_top : Subgroup.centralizer ({z} : Set H) ≠ ⊤ := by
      intro htop
      refine hz1 ?_
      have hz_center : z ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro w
        have hw : w ∈ Subgroup.centralizer ({z} : Set H) := htop ▸ Subgroup.mem_top w
        exact (Subgroup.mem_centralizer_iff.mp hw z (Set.mem_singleton z)).symm
      rw [hcenter_bot, Subgroup.mem_bot] at hz_center; exact hz_center
    obtain ⟨X, hX_coatom, hCzX⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom
        (Subgroup.centralizer ({z} : Set H))).resolve_left hCz_ne_top
    exact (hZ_unique X hX_coatom (hZ_le_Cz.trans hCzX)) ▸ hCzX
  -- L4. `S ∈ Syl_p(M)` (as an `H`-subgroup) is not a full Sylow `p` of `H`
  -- (it normalizes the nontrivial `q`-group `Z_q`, Step 2), so `N_P(S) > S`.
  obtain ⟨SM⟩ : Nonempty (Sylow p ↥M) := inferInstance
  set SH : Subgroup H := (SM : Subgroup ↥M).map M.subtype with hSH_def
  have hSH_le_M : SH ≤ M := by rw [hSH_def]; exact Subgroup.map_subtype_le _
  have hSH_pgroup : IsPGroup p SH := by rw [hSH_def]; exact SM.isPGroup'.map M.subtype
  have hZp_le_SM : Zp ≤ (SM : Subgroup ↥M) :=
    le_trans (by rw [hZp_def]; unfold zCenterOpCoreSubgroup; exact Subgroup.map_subtype_le _)
      (OddOrder.Isaacs.Ch01.opCore_le SM)
  have hZpH_le_SH : ZpH ≤ SH := by rw [hZpH_eq, hSH_def]; exact Subgroup.map_mono hZp_le_SM
  have hp_dvd_H : p ∣ Nat.card H := hp_dvd_Z.trans (Subgroup.card_subgroup_dvd_card Z)
  obtain ⟨P, hSHP⟩ := hSH_pgroup.exists_le_sylow
  have hSH_lt : SH < (P : Subgroup H) := by
    rcases eq_or_lt_of_le hSHP with h | h
    · exact absurd (h ▸ (le_trans hSH_le_M hM_norm_ZqH))
        (fun hPnorm => step2_pSylow_not_normalizes_nontrivial_qSubgroup hpq hH_card
          hp_dvd_H P hZqH_ne_bot hZqH_qgroup hPnorm)
    · exact h
  have hNPS_gt : SH < Subgroup.normalizer SH ⊓ (P : Subgroup H) :=
    lt_normalizer_inf_sylow_of_lt P hSH_lt
  set NPS : Subgroup H := Subgroup.normalizer SH ⊓ (P : Subgroup H) with hNPS_def
  -- `N_P(S) ⊄ M` (else it is a `p`-subgroup of `M` strictly containing the Sylow-`p`
  -- `S` of `M`, impossible by `Sylow.is_maximal'`); pick `g ∈ N_P(S) ∖ M`.
  have hNPS_not_le_M : ¬ NPS ≤ M := by
    intro hle
    have hNPS_pgroup : IsPGroup p NPS := by rw [hNPS_def]; exact P.isPGroup'.to_inf_right
    have hSM_le_K : (SM : Subgroup ↥M) ≤ NPS.comap M.subtype := by
      rw [← Subgroup.map_le_iff_le_comap, ← hSH_def]; exact le_of_lt hNPS_gt
    have hK_pgroup : IsPGroup p (NPS.comap M.subtype) :=
      hNPS_pgroup.comap_of_ker_isPGroup M.subtype
        (by rw [Subgroup.ker_subtype]; exact IsPGroup.of_bot)
    have hK_eq := SM.is_maximal' hK_pgroup hSM_le_K
    have hNPS_eq_SH : NPS = SH := by
      have h1 : (NPS.comap M.subtype).map M.subtype = NPS :=
        Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hle)
      rw [hK_eq] at h1
      exact (hSH_def.trans h1).symm
    exact (ne_of_lt hNPS_gt) hNPS_eq_SH.symm
  obtain ⟨g, hg_NPS, hg_notM⟩ := SetLike.not_le_iff_exists.mp hNPS_not_le_M
  rw [hNPS_def, Subgroup.mem_inf] at hg_NPS
  have hg_normSH : g ∈ Subgroup.normalizer SH := hg_NPS.1
  -- L5. `A := Z_p^g ⊆ S^g = S ⊆ M`, normalizing `Z_q`.
  set A : Subgroup H := ConjAct.toConjAct g • ZpH with hA_def
  have hA_le_SH : A ≤ SH := by
    rw [hA_def, ← Subgroup.conjAct_pointwise_smul_eq_self hg_normSH]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hZpH_le_SH
  have hA_le_M : A ≤ M := hA_le_SH.trans hSH_le_M
  have hA_norm_Zq : A ≤ Subgroup.normalizer ZqH := hA_le_M.trans hM_norm_ZqH
  -- A's algebraic properties via the conjugation iso `ZpH ≃* A`.
  have eA : ZpH ≃* A := by rw [hA_def]; exact Subgroup.equivSMul (ConjAct.toConjAct g) ZpH
  have hcardA : Nat.card ↥A = Nat.card ↥ZpH := Nat.card_congr eA.symm.toEquiv
  have hA_pgroup : IsPGroup p A := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥ZpH)).mp hZpH_pgroup
    exact IsPGroup.iff_card.mpr ⟨n, by rw [hcardA, hn]⟩
  haveI hZpH_nt : Nontrivial ↥ZpH := ZpH.nontrivial_iff_ne_bot.mpr hZpH_ne_bot
  haveI hA_nt : Nontrivial ↥A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardA]
    exact Finite.one_lt_card_iff_nontrivial.mpr hZpH_nt
  have hA_ne_bot : A ≠ ⊥ := A.nontrivial_iff_ne_bot.mp hA_nt
  haveI hA_comm : IsMulCommutative A :=
    ⟨⟨fun x y => eA.symm.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  -- L6 prerequisites: `N_H(M) = M` (M maximal in simple H), and `M^g := M.map (conj g)`
  -- is again maximal.
  have hNM_eq_M : Subgroup.normalizer M = M := by
    rcases eq_or_lt_of_le (show M ≤ Subgroup.normalizer M from Subgroup.le_normalizer) with h | h
    · exact h.symm
    · exfalso
      have hNtop : Subgroup.normalizer M = ⊤ := hM_max.2 _ h
      have hMnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M hMnorm with hb | ht
      · exact (M.nontrivial_iff_ne_bot.mp inferInstance) hb
      · exact hM_max.1 ht
  set Mg : Subgroup H := M.map (MulAut.conj g) with hMg_def
  have hMg_coatom : IsCoatom Mg := by
    rw [hMg_def]
    exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g)) M).mpr hM_max
  -- Membership in `M^g`, and the bridge `M^g = M ⇒ g ∈ N_H(M) = M`.
  have hmem_Mg : ∀ x : H, x ∈ Mg ↔ g⁻¹ * x * g ∈ M := fun x => by
    rw [hMg_def, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      change g⁻¹ * (MulAut.conj g m) * g ∈ M
      rw [MulAut.conj_apply, show g⁻¹ * (g * m * g⁻¹) * g = m from by group]
      exact hm
    · intro hx
      refine ⟨g⁻¹ * x * g, hx, ?_⟩
      change MulAut.conj g (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]; group
  have hg_in_M_of_Mg_eq : Mg = M → g ∈ M := fun hMgM => by
    rw [← hNM_eq_M, Subgroup.mem_normalizer_iff'']
    intro y; rw [← hmem_Mg y, hMgM]
  -- The conjugation action of `A` on `Z_q`, and coprimality of `|A|`, `|Z_q|`.
  letI : MulDistribMulAction ↥A ↥ZqH := conjActionOfNormalizes A ZqH hA_norm_Zq
  set φ : ↥A →* MulAut ↥ZqH := MulDistribMulAction.toMulAut ↥A ↥ZqH with hφ_def
  have hsmul_coe : ∀ (a : ↥A) (n : ↥ZqH), ((a • n : ↥ZqH) : H) = (↑a) * (↑n) * (↑a)⁻¹ :=
    fun _ _ => rfl
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥ZqH) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p) (G := ↥A)).mp hA_pgroup
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q) (G := ↥ZqH)).mp hZqH_qgroup
    rw [hm, hn]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp_prime hq_prime).mpr hpq)
  -- L6 key: for `1 ≠ a ∈ A`, anything commuting with `a` lies in `M^g`.
  -- Write `a = g z g⁻¹` with `1 ≠ z ∈ Z_p ⊆ Z`; then `C_H(a) = C_H(z)^g ⊆ M^g`
  -- since `C_H(z) ⊆ M` (L3).
  have hcomm_mem_Mg : ∀ a : H, a ∈ A → a ≠ 1 → ∀ x : H, a * x = x * a → x ∈ Mg := by
    intro a ha ha1 x hax
    rw [hA_def, Subgroup.mem_smul_pointwise_iff_exists] at ha
    obtain ⟨z, hz, hza⟩ := ha
    rw [ConjAct.toConjAct_smul] at hza
    have hz1 : z ≠ 1 := by
      rintro rfl
      exact ha1 (by rw [← hza]; group)
    rw [hmem_Mg]
    refine hL3 z (hZpH_le_Z hz) hz1 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw; subst w
    have h : g * z * g⁻¹ * x = x * (g * z * g⁻¹) := by rw [hza]; exact hax
    calc z * (g⁻¹ * x * g)
        = g⁻¹ * (g * z * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * z * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * x * g) * z := by group
  -- `Z_p ⊆ S = S^g ⊆ M^g` (`g` normalizes `S`, `S ⊆ M`).
  have hZpH_le_Mg : ZpH ≤ Mg := fun z hz => by
    rw [hmem_Mg]
    exact hSH_le_M ((Subgroup.mem_normalizer_iff''.mp hg_normSH z).mp (hZpH_le_SH hz))
  -- If `Z_q ⊆ M^g` then `Z ⊆ M^g`, so `M^g = M` (uniqueness), so `g ∈ N_H(M) = M`: absurd.
  have hZqH_le_Mg_imp_False : ZqH ≤ Mg → False := by
    intro hZqH_le_Mg
    have hZ_le_Mg : Z ≤ Mg := sup_le hZpH_le_Mg hZqH_le_Mg
    exact hg_notM (hg_in_M_of_Mg_eq (hZ_unique Mg hMg_coatom hZ_le_Mg))
  -- L7. **Dichotomy** (Isaacs L3987-3993). If `A` is non-cyclic, or acts non-faithfully on
  -- `Z_q`, then `Z_q = ⟨C_{Z_q}(a) : 1≠a∈A⟩ ⊆ M^g`, contradicting L6.  So `A` is cyclic and
  -- faithful.  Bridge: `⟨C_{Z_q}(a)⟩ = ⊤` (internally in `Z_q`) ⇒ `Z_q ⊆ M^g`, via L6's
  -- `hcomm_mem_Mg` (`C_G(a) ⊆ M^g`) applied to each generator.
  have hclosure_imp : nontrivialActionFixedByClosure φ = ⊤ → ZqH ≤ Mg := by
    intro htop w hw
    have hle : nontrivialActionFixedByClosure φ ≤ Mg.comap ZqH.subtype := by
      rw [nontrivialActionFixedByClosure_le_iff]
      intro c hc n hn
      rw [Subgroup.mem_comap]
      -- `n ∈ C_{Z_q}(c)` ⇒ `↑n` commutes with `↑c`, so `↑n ∈ M^g` by L6.
      have hsm : c • n = n := hn
      have hcoe := hsmul_coe c n
      rw [hsm] at hcoe
      have hcomm : (↑c : H) * ↑n = ↑n * ↑c := by
        have h := hcoe.symm
        calc (↑c : H) * ↑n = ((↑c : H) * ↑n * (↑c)⁻¹) * ↑c := by group
          _ = ↑n * ↑c := by rw [h]
      exact hcomm_mem_Mg ↑c c.2 (fun h => hc (OneMemClass.coe_eq_one.mp h)) ↑n hcomm
    have hmem : (⟨w, hw⟩ : ↥ZqH) ∈ Mg.comap ZqH.subtype := by
      rw [htop] at hle; exact hle (Subgroup.mem_top _)
    rwa [Subgroup.mem_comap] at hmem
  -- `A` is cyclic: else Thm 6.21 (`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic`)
  -- gives `⟨C_{Z_q}(a)⟩ = ⊤`, hence `Z_q ⊆ M^g` — contradiction with L6.
  have hA_cyclic : IsCyclic ↥A := by
    by_contra hnc
    refine hZqH_le_Mg_imp_False (hclosure_imp ?_)
    rw [hφ_def]
    exact nontrivialActionFixedByClosure_eq_top_of_not_isCyclic hcop hnc
  -- `A` acts faithfully on `Z_q`: else some `1 ≠ c ∈ A` fixes all of `Z_q`
  -- (`C_{Z_q}(c) = ⊤`), so again `⟨C_{Z_q}(a)⟩ = ⊤` and `Z_q ⊆ M^g` — contradiction.
  have hA_faithful : Function.Injective φ := by
    by_contra hni
    rw [injective_iff_map_eq_one] at hni
    push Not at hni
    obtain ⟨c, hc1, hc_ne⟩ := hni
    refine hZqH_le_Mg_imp_False (hclosure_imp ?_)
    have hfix_top : actionFixedBy φ c = ⊤ := by
      ext n; rw [mem_actionFixedBy, hc1]; simp
    rw [eq_top_iff, ← hfix_top]
    exact actionFixedBy_le_nontrivialActionFixedByClosure hc_ne
  -- Conclusion: `A ≅ Z_p` (so `Z_p` cyclic); and a faithful nontrivial `p`-group acting on
  -- the cyclic `Z_q` forces `p < q` (arithmetic helper).
  haveI := hA_cyclic
  refine ⟨isCyclic_of_surjective eA.symm.toMonoidHom eA.symm.surjective, fun hZq_cyc => ?_⟩
  haveI := hZq_cyc
  exact prime_lt_of_pGroup_faithful_on_cyclic hA_pgroup hA_nt hZqH_qgroup hpq φ hA_faithful

/-- **§7D Step 3** (Isaacs L3982-3993) — *not both cores nontrivial*.

For a maximal subgroup `M` of a simple group of order `p^a q^b`, it is **not**
the case that both `O_p(M)` and `O_q(M)` are nontrivial.  Combined with the
partition `maximal_isPType_or_isQType`, this gives: every maximal is `p`-type
**XOR** `q`-type.

Textbook proof: assuming both nontrivial, set `Z = Z(O_p(M)) · Z(O_q(M))`
(abelian, normal in `M`); then `M = N_G(Z)` is the unique maximal containing `Z`
(Step 1).  A Sylow `p`-subgroup `S` of `M` normalizes the nontrivial `q`-group
`Z_q`, so by Step 2 `S` is not a full Sylow `p`; the `N_P(S) > S` argument
produces `g ∈ G - M` with `S^g = S`, forcing `Z^g ⊆ M^g` and (via Thm 6.20 /
faithful-action analysis) `Z ⊆ M^g`, so `M = M^g` and `g ∈ M`, contradiction.

**Now a theorem** (was an axiom): applies the asymmetric core `step3_main` with
`(p,q)` and `(q,p)` for the same `M`, yielding `p < q` and `q < p`. -/
theorem step3_not_both_opCore_ne_bot
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_max : IsCoatom M) :
    OddOrder.Isaacs.Ch01.opCore p ↥M = ⊥ ∨ OddOrder.Isaacs.Ch01.opCore q ↥M = ⊥ := by
  by_contra h
  push Not at h
  obtain ⟨hOp, hOq⟩ := h
  obtain ⟨hZp_cyc, h_imp_pq⟩ := step3_main hpq hH_card hSubgroupsSolvable hM_max hOp hOq
  obtain ⟨hZq_cyc, h_imp_qp⟩ :=
    step3_main hpq.symm (by rw [mul_comm]; exact hH_card) hSubgroupsSolvable hM_max hOq hOp
  have hpq_lt : p < q := h_imp_pq hZq_cyc
  have hqp_lt : q < p := h_imp_qp hZp_cyc
  omega

/-- **§7D Steps 2-3 dichotomy** (Isaacs L4022-4026) — *every maximal subgroup
has exactly one type*.

Combining the partition (`maximal_isPType_or_isQType`, proven) with Step 3
(`step3_not_both_opCore_ne_bot`, axiom: not both cores nontrivial): a maximal
subgroup `M ≠ ⊥` of a simple group of order `p^a q^b` is `p`-type **xor**
`q`-type — exactly one of `IsPType p M`, `IsQType q M` holds.  This `Xor` form
is the precise statement used throughout Steps 5-9. -/
theorem maximal_isPType_xor_isQType
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_max : IsCoatom M) (hM_ne_bot : M ≠ ⊥) :
    Xor (IsPType p M) (IsQType q M) := by
  -- At least one type (partition).
  have h_or : IsPType p M ∨ IsQType q M :=
    maximal_isPType_or_isQType hpq hH_card hM_max hM_ne_bot (hSubgroupsSolvable M hM_max.1)
  -- Not both (Step 3): O_p(M) = ⊥ ∨ O_q(M) = ⊥.
  have h_step3 : OddOrder.Isaacs.Ch01.opCore p ↥M = ⊥ ∨ OddOrder.Isaacs.Ch01.opCore q ↥M = ⊥ :=
    step3_not_both_opCore_ne_bot hpq hH_card hSubgroupsSolvable hM_max
  -- IsPType p M = (IsCoatom M ∧ O_p(M) ≠ ⊥); IsQType q M = (IsCoatom M ∧ O_q(M) ≠ ⊥).
  have h_not_both : ¬ (IsPType p M ∧ IsQType q M) := by
    rintro ⟨hP, hQ⟩
    rcases h_step3 with hp_bot | hq_bot
    · exact hP.2 hp_bot
    · exact hQ.2 hq_bot
  rcases h_or with hP | hQ
  · exact Or.inl ⟨hP, fun hQ => h_not_both ⟨hP, hQ⟩⟩
  · exact Or.inr ⟨hQ, fun hP => h_not_both ⟨hP, hQ⟩⟩

/-- **§7D Step 8 helper** — for a `p`-type maximal `M` of a simple group of order
`p^a q^b`, the `p'`-core of `M` is trivial: `O_{p'}(M) = ⊥`.

`O_{p'}(M) = oPiCore {r ≠ p} ↥M` is a normal `{r ≠ p}`-subgroup of `↥M`.  Since
`|M| ∣ p^a q^b`, its only prime factors lie in `{p, q}`; intersecting with
`{r ≠ p}` leaves only `q`, so `O_{p'}(M)` is a `q`-group, hence `≤ O_q(M)`.  By
the dichotomy, `M` `p`-type ⇒ `O_q(M) = ⊥`. -/
theorem oPiCore_pPrime_eq_bot_of_isPType
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M) :
    OddOrder.Isaacs.Ch03.oPiCore {r | r ≠ p} ↥M = ⊥ := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    have : Subsingleton ↥M := by rw [hMbot]; infer_instance
    exact hM_pType.2 (Subgroup.eq_bot_of_subsingleton _)
  -- `O_q(M) = ⊥` by the dichotomy (`M` p-type ⇒ not q-type ⇒ O_q(M) = ⊥).
  have hOq_bot : OddOrder.Isaacs.Ch01.opCore q ↥M = ⊥ := by
    rcases maximal_isPType_xor_isQType hpq hH_card hSubgroupsSolvable hM_pType.1 hM_ne_bot with
      h | h
    · by_contra hne
      exact h.2 ⟨hM_pType.1, hne⟩
    · exact absurd hM_pType h.2
  set K := OddOrder.Isaacs.Ch03.oPiCore {r | r ≠ p} ↥M with hK_def
  have hM_card_dvd : Nat.card ↥M ∣ p ^ a * q ^ b := by
    rw [← hH_card]; exact M.card_subgroup_dvd_card
  have hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {r | r ≠ p} K :=
    OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {r | r ≠ p}
  -- `K` is a `q`-group: any prime factor `r ∣ |K|` is `≠ p`, divides `|M| ∣ p^a q^b`,
  -- hence `r = q`.
  have hK_q_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({q} : Set ℕ) K := by
    intro r hr
    obtain ⟨hr_prime, hr_dvd_K, _⟩ := Nat.mem_primeFactors.mp hr
    have hr_ne_p : r ≠ p := hK_pi r hr
    have hr_dvd_M : r ∣ Nat.card ↥M := hr_dvd_K.trans K.card_subgroup_dvd_card
    have hr_dvd_paqb : r ∣ p ^ a * q ^ b := hr_dvd_M.trans hM_card_dvd
    rcases (Nat.Prime.dvd_mul hr_prime).mp hr_dvd_paqb with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp
        (hr_prime.dvd_of_dvd_pow h)) hr_ne_p
    · simp only [Set.mem_singleton_iff]
      exact (Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp (hr_prime.dvd_of_dvd_pow h)
  have hK_qgroup : IsPGroup q K :=
    OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton hK_q_pi
  haveI : K.Normal := OddOrder.Isaacs.Ch03.oPiCore.normal {r | r ≠ p} ↥M
  have hK_le : K ≤ OddOrder.Isaacs.Ch01.opCore q ↥M :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hK_qgroup
  rw [hOq_bot, le_bot_iff] at hK_le
  exact hK_le

/-- **§7D Step 4** — `U⋆`, the subgroup generated by the `p`-central elements of a
subgroup `U`. -/
def pCentralGenerated (p : ℕ) {G : Type*} [Group G] (U : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ U ∧ IsPCentral p x}

/-- `U⋆ ≤ U`. -/
theorem pCentralGenerated_le {p : ℕ} {G : Type*} [Group G] (U : Subgroup G) :
    pCentralGenerated p U ≤ U := by
  rw [pCentralGenerated, Subgroup.closure_le]
  intro x hx; exact hx.1

/-- A `p`-central element of `U` lies in `U⋆`. -/
theorem mem_pCentralGenerated {p : ℕ} {G : Type*} [Group G] {U : Subgroup G} {x : G}
    (hxU : x ∈ U) (hx : IsPCentral p x) : x ∈ pCentralGenerated p U :=
  Subgroup.subset_closure ⟨hxU, hx⟩

/-- `N_G(U)` normalizes `U⋆`: for `g ∈ N_G(U)`, `g • U⋆ = U⋆`. -/
theorem pCentralGenerated_normalized_by_normalizer {p : ℕ} {G : Type*} [Group G] [Finite G]
    [Fact p.Prime] {U : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    (pCentralGenerated p U).map (MulAut.conj g).toMonoidHom = pCentralGenerated p U := by
  -- closure of S maps to closure of (conj g '' S); show conj g '' S = S as sets where
  -- S = {x ∈ U ∧ p-central}.  g permutes U (g ∈ N_G(U)) and preserves p-centrality.
  rw [pCentralGenerated, MonoidHom.map_closure]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨hxU, hx_pc⟩, rfl⟩
    refine ⟨?_, hx_pc.conj g⟩
    -- g x g⁻¹ ∈ U since g ∈ N_G(U).
    rw [Subgroup.mem_normalizer_iff] at hg
    exact (hg x).mp hxU
  · intro ⟨hzU, hz_pc⟩
    -- z = g (g⁻¹ z g) g⁻¹, and g⁻¹ z g ∈ U, p-central.
    refine ⟨g⁻¹ * z * g, ⟨?_, ?_⟩, ?_⟩
    · -- g⁻¹ z g ∈ U: g⁻¹ ∈ N_G(U), apply mem_normalizer_iff.
      have hg_inv : g⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
        (Subgroup.normalizer (U : Set G)).inv_mem hg
      rw [Subgroup.mem_normalizer_iff] at hg_inv
      have := (hg_inv z).mp hzU
      simpa using this
    · have := hz_pc.conj g⁻¹
      simpa using this
    · change g * (g⁻¹ * z * g) * g⁻¹ = z; group

/-- `(U⋆)⋆ = U⋆`: the `p`-central-generated subgroup is idempotent. -/
theorem pCentralGenerated_idem {p : ℕ} {G : Type*} [Group G] (U : Subgroup G) :
    pCentralGenerated p (pCentralGenerated p U) = pCentralGenerated p U := by
  apply le_antisymm (pCentralGenerated_le _)
  rw [pCentralGenerated, Subgroup.closure_le]
  intro x hx
  obtain ⟨hxU, hx_pc⟩ := hx
  have hx_in_Ustar : x ∈ pCentralGenerated p U := mem_pCentralGenerated hxU hx_pc
  exact mem_pCentralGenerated hx_in_Ustar hx_pc

/-- **§7D Step 4** (Isaacs L4001-4019) — *a `q`-central element normalizing a
`p`-subgroup forbids `p`-central elements*.  **Now a theorem** (the `W`-maximality
argument; was an axiom).

If `y` is `q`-central, `V` a `p`-subgroup of the simple group `H` (order
`p^a q^b`) normalized by `y`, and `x ∈ V` is `p`-central, this is contradictory.

Proof: `W` is chosen maximal among nontrivial `p`-subgroups that are
`y`-normalized and self-`p`-central-generated (`V⋆ ∋ x` witnesses nonemptiness).
Set `N = N_H(W)`, `S ∈ Syl_p(N)`; `⟨y⟩ ⊔ P = H` for every Sylow `p` `P` (Step 2
reversed, `Q ∋ y` normalizes `⟨y⟩`), so since `⟨y, S⟩ ≤ N < H`, `S` is not a full
Sylow `p`.  The normalizer condition in a containing Sylow gives `g ∈ N_H(S) \ N`,
whence `W^g ≠ W`, `W^g ≤ S ≤ N`; a `p`-central generator `x'` of `W` with
`x'^g ∉ W` exists.  Writing `g = b·a` (`b ∈ Q`, `a ∈ P'` with `x' ∈ Z(P')`),
`g x' g⁻¹ = b x' b⁻¹ =: z` is a `p`-central element of `W^b ⊓ N`.  Then
`(W ⊔ (W^b ⊓ N))⋆` is a `y`-normalized, self-`p`-central-generated `p`-subgroup
strictly containing `W` (it contains `z ∉ W`), contradicting maximality. -/
theorem step4_qCentral_normalizes_no_pCentral
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (_hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {y : H} (hy_qcentral : IsPCentral q y)
    {V : Subgroup H} (hV_pgroup : IsPGroup p V)
    (hy_norm : y ∈ Subgroup.normalizer V)
    {x : H} (hx_pcentral : IsPCentral p x) (hx_mem : x ∈ V) :
    False := by
  classical
  letI : Fintype (Subgroup H) := Fintype.ofFinite _
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  have hH_card_swap : Nat.card H = q ^ b * p ^ a := by rw [hH_card]; ring
  -- The family: p-subgroups W with y ∈ N_G(W) and W = pCentralGenerated p W.
  -- V⋆ is in the family and nontrivial.
  set Vstar : Subgroup H := pCentralGenerated p V with hVstar_def
  have hx_in_Vstar : x ∈ Vstar := mem_pCentralGenerated hx_mem hx_pcentral
  have hVstar_ne_bot : Vstar ≠ ⊥ := by
    intro hbot; rw [hbot] at hx_in_Vstar
    exact hx_pcentral.ne_one (Subgroup.mem_bot.mp hx_in_Vstar)
  -- Family as a Finset.
  let family : Finset (Subgroup H) :=
    Finset.univ.filter (fun W => W ≠ ⊥ ∧ IsPGroup p W ∧
      y ∈ Subgroup.normalizer (W : Set H) ∧ pCentralGenerated p W = W)
  -- Vstar ∈ family.
  have hVstar_pgroup : IsPGroup p Vstar :=
    hV_pgroup.of_injective (Subgroup.inclusion (pCentralGenerated_le V))
      (Subgroup.inclusion_injective _)
  have hy_norm_Vstar : y ∈ Subgroup.normalizer (Vstar : Set H) := by
    -- y ∈ N_G(V) ⇒ y normalizes V⋆.
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h := pCentralGenerated_normalized_by_normalizer (p := p) (U := V) hy_norm
    constructor
    · intro hz
      have : y * z * y⁻¹ ∈ (pCentralGenerated p V).map (MulAut.conj y).toMonoidHom := ⟨z, hz, rfl⟩
      rw [h] at this; exact this
    · intro hz
      have : y * z * y⁻¹ ∈ (pCentralGenerated p V).map (MulAut.conj y).toMonoidHom := by
        rw [h]; exact hz
      obtain ⟨w, hw, hweq⟩ := this
      have hweq' : y * w * y⁻¹ = y * z * y⁻¹ := hweq
      have : z = w := (mul_left_cancel (mul_right_cancel hweq')).symm
      rw [this]; exact hw
  have hVstar_selfgen : pCentralGenerated p Vstar = Vstar :=
    pCentralGenerated_idem V
  have hVstar_mem : Vstar ∈ family := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hVstar_ne_bot, hVstar_pgroup, hy_norm_Vstar, hVstar_selfgen⟩
  have hne : family.Nonempty := ⟨Vstar, hVstar_mem⟩
  -- Maximal W by order.
  obtain ⟨W, hW_mem, hW_max⟩ := family.exists_max_image (fun W => Nat.card W) hne
  obtain ⟨hW_ne_bot, hW_pgroup, hy_norm_W, hW_selfgen⟩ := Finset.mem_filter.mp hW_mem |>.2
  -- hW_max as a function on the family.
  have hmaxW : ∀ W' : Subgroup H, W' ≠ ⊥ → IsPGroup p W' →
      y ∈ Subgroup.normalizer (W' : Set H) → pCentralGenerated p W' = W' →
      Nat.card W' ≤ Nat.card W := by
    intro W' h1 h2 h3 h4
    exact hW_max W' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3, h4⟩)
  -- N := N_H(W).
  set N : Subgroup H := Subgroup.normalizer (W : Set H) with hN_def
  have hW_le_N : W ≤ N := Subgroup.le_normalizer
  -- N < H (else W ⊴ H, simple ⇒ W ∈ {⊥,⊤}; W ≠ ⊥; W = ⊤ ⇒ H p-group ⇒ contra).
  have hN_ne_top : N ≠ ⊤ := by
    intro hNtop
    have hW_normal : W.Normal := by
      rw [hN_def, Subgroup.normalizer_eq_top_iff] at hNtop; exact hNtop
    rcases hW_normal.eq_bot_or_eq_top with hb | ht
    · exact hW_ne_bot hb
    · -- W = ⊤ ⇒ H p-group ⇒ q ∤ |H|.
      have hH_pgroup : IsPGroup p H := by
        have : IsPGroup p (⊤ : Subgroup H) := ht ▸ hW_pgroup
        exact this.of_equiv Subgroup.topEquiv
      obtain ⟨k, hk⟩ := hH_pgroup.exists_card_eq
      rw [hk] at hq_dvd
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp
        (hq_prime.dvd_of_dvd_pow hq_dvd)).symm
  -- y ∈ N.
  have hy_in_N : y ∈ N := hy_norm_W
  -- S : Sylow p of ↥N, with W.subgroupOf N ≤ S; S_H := image ⊇ W.
  have hW_subN_p : IsPGroup p (W.subgroupOf N) := hW_pgroup.comap_subtype
  obtain ⟨S, hWsub_le_S⟩ := hW_subN_p.exists_le_sylow
  set SH : Subgroup H := (S : Subgroup ↥N).map N.subtype with hSH_def
  have hSH_p : IsPGroup p SH := S.isPGroup'.map N.subtype
  have hSH_le_N : SH ≤ N := by rw [hSH_def]; exact Subgroup.map_subtype_le _
  have hW_le_SH : W ≤ SH := by
    intro w hw
    have : (⟨w, hW_le_N hw⟩ : ↥N) ∈ (S : Subgroup ↥N) := by
      apply hWsub_le_S; rw [Subgroup.mem_subgroupOf]; exact hw
    exact ⟨⟨w, hW_le_N hw⟩, this, rfl⟩
  -- SH is not a full Sylow p of H (Step 2 reversed with V = ⟨y⟩).
  have hSH_not_full : ∀ P : Sylow p H, SH ≠ (P : Subgroup H) := by
    intro P hSHP
    -- ⟨y⟩ ⊔ P = ⊤ (Step 2 reversed); but SH = P ≤ N < H and y ∈ N ⇒ ⟨y⟩ ⊔ P ≤ N.
    obtain ⟨hy_ne, Q, ⟨yv, hyv_mem⟩, hyv_center, hyv_eq⟩ := hy_qcentral
    simp only [Subgroup.coe_subtype] at hyv_eq
    -- y central in Q: every qg ∈ Q commutes with y.
    have hyQ_comm : ∀ qg ∈ (Q : Subgroup H), qg * y = y * qg := by
      intro qg hqg
      have hcen := (Subgroup.mem_center_iff.mp hyv_center) ⟨qg, hqg⟩
      have h2 := congrArg (Subgroup.subtype (Q : Subgroup H)) hcen
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at h2
      -- h2 : qg * yv = yv * qg ; yv = y.
      rw [hyv_eq] at h2
      exact h2
    -- Q ≤ C_H(⟨y⟩) ≤ N_H(⟨y⟩): qg commutes with y ⇒ with all of ⟨y⟩.
    have hQ_norm_y : (Q : Subgroup H) ≤ Subgroup.normalizer (Subgroup.zpowers y) := by
      intro qg hqg
      apply centralizer_le_normalizer (Subgroup.zpowers y)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hc : Commute qg y := hyQ_comm qg hqg
      have : Commute (y ^ k) qg := (hc.symm.zpow_left k)
      exact this
    have hy_ne_bot : Subgroup.zpowers y ≠ ⊥ := by
      intro hb
      have : y ∈ (⊥ : Subgroup H) := hb ▸ Subgroup.mem_zpowers y
      exact hy_ne (Subgroup.mem_bot.mp this)
    -- Step 2 reversed: ⟨y⟩ ⊔ P = ⊤.
    have htop : Subgroup.zpowers y ⊔ (P : Subgroup H) = ⊤ :=
      step2_join_sylow_q_eq_top (p := q) (q := p) (Ne.symm hpq) hH_card_swap
        Q P hy_ne_bot hQ_norm_y
    -- But ⟨y⟩ ⊔ P ≤ N: y ∈ N, P = SH ≤ N.
    have hyP_le_N : Subgroup.zpowers y ⊔ (P : Subgroup H) ≤ N := by
      apply sup_le
      · rw [Subgroup.zpowers_le]; exact hy_in_N
      · rw [← hSHP]; exact hSH_le_N
    rw [htop, top_le_iff] at hyP_le_N
    exact hN_ne_top hyP_le_N
  -- (a) SH < PH (full Sylow); N_H(SH) ⊓ PH ⊋ SH and ⊄ N ⇒ ∃ g ∈ N_H(SH)\N.
  obtain ⟨PH, hSH_le_PH⟩ := IsPGroup.exists_le_sylow hSH_p
  have hSH_lt_PH : SH < (PH : Subgroup H) :=
    lt_of_le_of_ne hSH_le_PH (hSH_not_full PH)
  have hSH_lt_norm : SH < Subgroup.normalizer (SH : Set H) ⊓ (PH : Subgroup H) :=
    lt_normalizer_inf_sylow_of_lt PH hSH_lt_PH
  -- SH is a Sylow p of ↥N (it's a maximal p-subgroup of N).  So any p-subgroup of N
  -- containing SH equals SH.  N_H(SH) ⊓ PH is a p-subgroup ⊋ SH ⇒ it is not ≤ N.
  have hNormPH_not_le_N : ¬ (Subgroup.normalizer (SH : Set H) ⊓ (PH : Subgroup H) ≤ N) := by
    intro hle
    -- Then (N_H(SH) ⊓ PH).subgroupOf N is a p-subgroup of N containing S.subgroupOf,
    -- so by Sylow maximality of S, it = S.subgroupOf, forcing equality, contra ⊋.
    set T : Subgroup H := Subgroup.normalizer (SH : Set H) ⊓ (PH : Subgroup H) with hT_def
    have hT_p : IsPGroup p T :=
      PH.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
        (Subgroup.inclusion_injective _)
    have hT_subN_p : IsPGroup p (T.subgroupOf N) := hT_p.comap_subtype
    have hS_le_T_subN : (S : Subgroup ↥N) ≤ T.subgroupOf N := by
      intro s hs
      rw [Subgroup.mem_subgroupOf]
      have hsH_mem : N.subtype s ∈ SH := ⟨s, hs, rfl⟩
      exact ⟨Subgroup.le_normalizer hsH_mem, hSH_le_PH hsH_mem⟩
    have hT_subN_eq : T.subgroupOf N = (S : Subgroup ↥N) := S.is_maximal' hT_subN_p hS_le_T_subN
    -- Then T = T ⊓ N (T ≤ N), and (T⊓N).subgroupOf N = T.subgroupOf N = S.subgroupOf;
    -- mapping back: T = SH, contra SH ⊊ T.
    have hT_map : (T.subgroupOf N).map N.subtype = T := by
      rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, N.range_subtype]
      exact inf_eq_right.mpr hle
    rw [hT_subN_eq] at hT_map
    -- hT_map : SH.map ... wait, (S:Subgroup ↥N).map subtype = SH by def.
    have : T = SH := by rw [← hT_map, hSH_def]
    rw [this] at hSH_lt_norm
    exact (lt_irrefl _ hSH_lt_norm)
  -- Choose g ∈ (N_H(SH) ⊓ PH) \ N.
  obtain ⟨g, hg_mem, hg_not_N⟩ := SetLike.not_le_iff_exists.mp hNormPH_not_le_N
  have hg_norm_SH : g ∈ Subgroup.normalizer (SH : Set H) := hg_mem.1
  -- (b) W^g ≠ W (else g ∈ N_H(W) = N); W^g ≤ SH.
  set Wg : Subgroup H := W.map (MulAut.conj g).toMonoidHom with hWg_def
  have hWg_ne_W : Wg ≠ W := by
    intro h
    apply hg_not_N
    -- W.map (conj g) = W ⇒ g ∈ N_H(W).
    rw [hN_def, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hmem : g * z * g⁻¹ ∈ Wg := by rw [hWg_def]; exact ⟨z, hz, rfl⟩
      rw [h] at hmem; exact hmem
    · intro hz
      have hmem2 : g * z * g⁻¹ ∈ Wg := by rw [h]; exact hz
      rw [hWg_def] at hmem2
      obtain ⟨w, hw, hweq⟩ := hmem2
      have hweq' : g * w * g⁻¹ = g * z * g⁻¹ := hweq
      have : z = w := (mul_left_cancel (mul_right_cancel hweq')).symm
      rw [this]; exact hw
  have hWg_le_SH : Wg ≤ SH := by
    rw [hWg_def]
    rw [Subgroup.mem_normalizer_iff] at hg_norm_SH
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (hg_norm_SH w).mp (hW_le_SH hw)
  -- (c) ∃ p-central generator x' of W with g x' g⁻¹ ∉ W.
  have hex_x : ∃ x' : H, x' ∈ W ∧ IsPCentral p x' ∧ g * x' * g⁻¹ ∉ W := by
    by_contra hall
    push Not at hall
    -- Then every p-central x' ∈ W has g x' g⁻¹ ∈ W ⇒ Wg ≤ W ⇒ (card) Wg = W.
    apply hWg_ne_W
    -- Wg = W.map(conj g); W = closure {p-central elts}; image ≤ W.
    have hWg_le_W : Wg ≤ W := by
      -- W = closure of its p-central elts; image of each generator under conj g lands in W.
      have hW_cl : W = Subgroup.closure {x : H | x ∈ W ∧ IsPCentral p x} := by
        rw [← pCentralGenerated]; exact hW_selfgen.symm
      have hWg_cl : Wg = Subgroup.closure ((MulAut.conj g).toMonoidHom ''
          {x : H | x ∈ W ∧ IsPCentral p x}) := by
        rw [hWg_def]; conv_lhs => rw [hW_cl]
        rw [MonoidHom.map_closure]
      rw [hWg_cl, Subgroup.closure_le]
      rintro z ⟨x', ⟨hx'W, hx'pc⟩, rfl⟩
      exact hall x' hx'W hx'pc
    -- |Wg| = |W| (conj iso) ⇒ Wg = W.
    have hcard_eq : Nat.card Wg = Nat.card W := by
      rw [hWg_def]
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective W _ (MulAut.conj g).injective).toEquiv).symm
    exact Subgroup.eq_of_le_of_card_ge hWg_le_W (le_of_eq hcard_eq.symm)
  obtain ⟨x', hx'W, hx'pc, hx'g_not_W⟩ := hex_x
  -- (d) decompose g = b * a (b ∈ Q, a ∈ P') with x' ∈ Z(P'); then g x' g⁻¹ = b x' b⁻¹.
  have hx'pc' : IsPCentral p x' := hx'pc
  obtain ⟨hx'_ne, P', hx'P'⟩ := hx'pc
  -- x' ∈ Z(P') : extract the centrality.
  obtain ⟨⟨x'v, hx'v_mem⟩, hx'v_center, hx'v_eq⟩ := hx'P'
  simp only [Subgroup.coe_subtype] at hx'v_eq
  -- a ∈ P' commutes with x'.
  have hP'_comm : ∀ av ∈ (P' : Subgroup H), av * x' = x' * av := by
    intro av hav
    have := (Subgroup.mem_center_iff.mp hx'v_center) ⟨av, hav⟩
    have h2 := congrArg (Subgroup.subtype (P' : Subgroup H)) this
    simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at h2
    rw [hx'v_eq] at h2; exact h2
  -- (Q, P') complement: g = b * a, b ∈ Q, a ∈ P'.  (Q from y-centrality.)
  obtain ⟨hy_ne2, Qy, ⟨yv2, hyv2_mem⟩, hyv2_center, hyv2_eq⟩ := hy_qcentral
  simp only [Subgroup.coe_subtype] at hyv2_eq
  have hcompl : Subgroup.IsComplement' (Qy : Subgroup H) (P' : Subgroup H) :=
    (sylow_isComplement_of_paqb hpq hH_card P' Qy).symm
  obtain ⟨⟨⟨b, hb⟩, ⟨av, hav⟩⟩, hba⟩ := hcompl.2 g
  simp only at hba
  -- g = b * av.
  -- g x' g⁻¹ = b x' b⁻¹ (av commutes with x').
  have hgx'g : g * x' * g⁻¹ = b * x' * b⁻¹ := by
    have hav_comm : av * x' = x' * av := hP'_comm av hav
    rw [← hba]
    calc b * av * x' * (b * av)⁻¹
        = b * (av * x') * (b * av)⁻¹ := by group
      _ = b * (x' * av) * (b * av)⁻¹ := by rw [hav_comm]
      _ = b * x' * b⁻¹ := by group
  -- z := g x' g⁻¹, lies in Wg ≤ SH ≤ N, and z = b x' b⁻¹ ∈ Wb := W.map(conj b).
  set z : H := g * x' * g⁻¹ with hz_def
  have hz_in_Wg : z ∈ Wg := by rw [hz_def, hWg_def]; exact ⟨x', hx'W, rfl⟩
  have hz_in_N : z ∈ N := hSH_le_N (hWg_le_SH hz_in_Wg)
  set Wb : Subgroup H := W.map (MulAut.conj b).toMonoidHom with hWb_def
  have hz_in_Wb : z ∈ Wb := by
    rw [hWb_def, hgx'g]; exact ⟨x', hx'W, rfl⟩
  set WbN : Subgroup H := Wb ⊓ N with hWbN_def
  have hz_in_WbN : z ∈ WbN := ⟨hz_in_Wb, hz_in_N⟩
  -- z is p-central (conjugate of x').
  have hz_pcentral : IsPCentral p z := hx'pc'.conj g
  -- W ⊴ N.
  haveI hW_normal_N : (W.subgroupOf N).Normal := by
    rw [hN_def]; exact Subgroup.normal_in_normalizer
  -- WW := W ⊔ WbN is a p-group (work in ↥N).
  set WW : Subgroup H := W ⊔ WbN with hWW_def
  have hWbN_le_N : WbN ≤ N := inf_le_right
  have hWb_p : IsPGroup p Wb := hW_pgroup.map (MulAut.conj b).toMonoidHom
  have hWbN_p : IsPGroup p WbN :=
    hWb_p.of_injective (Subgroup.inclusion (inf_le_left : WbN ≤ Wb))
      (Subgroup.inclusion_injective _)
  -- WW.subgroupOf N = W.subgroupOf N ⊔ WbN.subgroupOf N, a p-group in ↥N.
  have hWW_le_N : WW ≤ N := sup_le hW_le_N hWbN_le_N
  have hWsubN_p : IsPGroup p (W.subgroupOf N) := hW_pgroup.comap_subtype
  have hWbNsubN_p : IsPGroup p (WbN.subgroupOf N) := hWbN_p.comap_subtype
  have hWWsubN_p : IsPGroup p ((W.subgroupOf N) ⊔ (WbN.subgroupOf N) : Subgroup ↥N) :=
    IsPGroup.to_sup_of_normal_left hWsubN_p hWbNsubN_p
  -- big := (W.subgroupOf N ⊔ WbN.subgroupOf N).map subtype, a p-group ⊇ W, WbN, ≤ N.
  set big : Subgroup H := ((W.subgroupOf N) ⊔ (WbN.subgroupOf N)).map N.subtype with hbig_def
  have hbig_p : IsPGroup p big := hWWsubN_p.map N.subtype
  have hW_le_big : W ≤ big := by
    intro w hw
    exact ⟨⟨w, hW_le_N hw⟩, Subgroup.mem_sup_left (by rw [Subgroup.mem_subgroupOf]; exact hw), rfl⟩
  have hWbN_le_big : WbN ≤ big := by
    intro w hw
    exact ⟨⟨w, hWbN_le_N hw⟩,
      Subgroup.mem_sup_right (by rw [Subgroup.mem_subgroupOf]; exact hw), rfl⟩
  have hWW_le_big : WW ≤ big := sup_le hW_le_big hWbN_le_big
  have hWW_p : IsPGroup p WW :=
    hbig_p.of_injective (Subgroup.inclusion hWW_le_big) (Subgroup.inclusion_injective _)
  -- (e) y normalizes WW = W ⊔ WbN, via map(conj y) = self on each piece.
  -- Helper: membership in normalizer ↔ map(conj y) fixes the subgroup.
  have hmap_of_norm : ∀ (S : Subgroup H), y ∈ Subgroup.normalizer (S : Set H) →
      S.map (MulAut.conj y).toMonoidHom = S := by
    intro S hy
    have h1 : S.map (MulAut.conj y).toMonoidHom ≤ S := by
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_normalizer_iff] at hy
      exact (hy w).mp hw
    exact Subgroup.eq_of_le_of_card_ge h1 (le_of_eq
      (Nat.card_congr (Subgroup.equivMapOfInjective S _ (MulAut.conj y).injective).toEquiv))
  have hnorm_of_map : ∀ (S : Subgroup H), S.map (MulAut.conj y).toMonoidHom = S →
      y ∈ Subgroup.normalizer (S : Set H) := by
    intro S hmap
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have : y * w * y⁻¹ ∈ S.map (MulAut.conj y).toMonoidHom := ⟨w, hw, rfl⟩
      rw [hmap] at this; exact this
    · intro hw
      have hmem : y * w * y⁻¹ ∈ S.map (MulAut.conj y).toMonoidHom := by rw [hmap]; exact hw
      obtain ⟨w', hw', hw'eq⟩ := hmem
      have : w = w' := (mul_left_cancel (mul_right_cancel (hw'eq : y*w'*y⁻¹ = y*w*y⁻¹))).symm
      rw [this]; exact hw'
  -- y fixes W and WbN.
  have hWmap : W.map (MulAut.conj y).toMonoidHom = W := hmap_of_norm W hy_norm_W
  -- y normalizes WbN: y fixes Wb (since y b = b y) and N (y ∈ N).
  have hyb_comm : y * b = b * y := by
    have := (Subgroup.mem_center_iff.mp hyv2_center) ⟨b, hb⟩
    have h2 := congrArg (Subgroup.subtype (Qy : Subgroup H)) this
    simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at h2
    rw [hyv2_eq] at h2; exact h2.symm
  have hWbmap : Wb.map (MulAut.conj y).toMonoidHom = Wb := by
    -- Wb = W.map(conj b); conj y ∘ conj b = conj b ∘ conj y (y,b commute) and conj y fixes W.
    rw [hWb_def, Subgroup.map_map]
    have hcomm_maps : (MulAut.conj y).toMonoidHom.comp (MulAut.conj b).toMonoidHom
        = (MulAut.conj b).toMonoidHom.comp (MulAut.conj y).toMonoidHom := by
      ext w
      simp only [MonoidHom.comp_apply]
      calc y * (b * w * b⁻¹) * y⁻¹
          = (y * b) * w * (y * b)⁻¹ := by group
        _ = (b * y) * w * (b * y)⁻¹ := by rw [hyb_comm]
        _ = b * (y * w * y⁻¹) * b⁻¹ := by group
    rw [hcomm_maps, ← Subgroup.map_map, hWmap]
  have hNmap : N.map (MulAut.conj y).toMonoidHom = N :=
    hmap_of_norm N (Subgroup.le_normalizer hy_in_N)
  have hWbNmap : WbN.map (MulAut.conj y).toMonoidHom = WbN := by
    rw [hWbN_def, Subgroup.map_inf _ _ _ (MulAut.conj y).injective, hWbmap, hNmap]
  have hy_norm_WW : y ∈ Subgroup.normalizer (WW : Set H) := by
    apply hnorm_of_map
    rw [hWW_def, Subgroup.map_sup, hWmap, hWbNmap]
  -- (f) WW⋆ : p-subgroup, y-normalized, self-gen, nontrivial, ⊋ W ⇒ contra maximality.
  set WWstar : Subgroup H := pCentralGenerated p WW with hWWstar_def
  -- W ≤ WW⋆.
  have hW_le_WWstar : W ≤ WWstar := by
    rw [← hW_selfgen, pCentralGenerated, hWWstar_def, pCentralGenerated, Subgroup.closure_le]
    rintro w ⟨hwW, hwpc⟩
    exact Subgroup.subset_closure ⟨(le_sup_left : W ≤ WW) hwW, hwpc⟩
  -- z ∈ WW⋆ (z p-central, z ∈ WbN ≤ WW).
  have hz_in_WW : z ∈ WW := (le_sup_right : WbN ≤ WW) hz_in_WbN
  have hz_in_WWstar : z ∈ WWstar := mem_pCentralGenerated hz_in_WW hz_pcentral
  -- WW⋆ ≠ W (z ∈ WW⋆ \ W).
  have hWWstar_ne_W : WWstar ≠ W := by
    intro h; rw [h] at hz_in_WWstar; exact hx'g_not_W hz_in_WWstar
  -- WW⋆ properties.
  have hWWstar_p : IsPGroup p WWstar :=
    hWW_p.of_injective (Subgroup.inclusion (pCentralGenerated_le WW))
      (Subgroup.inclusion_injective _)
  have hWWstar_ne_bot : WWstar ≠ ⊥ := by
    intro hbot
    have : W ≤ (⊥ : Subgroup H) := hbot ▸ hW_le_WWstar
    rw [le_bot_iff] at this; exact hW_ne_bot this
  have hWWstar_norm : y ∈ Subgroup.normalizer (WWstar : Set H) := by
    -- N_H(WW) normalizes WW⋆.
    have hh := pCentralGenerated_normalized_by_normalizer (p := p) (U := WW) hy_norm_WW
    exact hnorm_of_map WWstar (by rw [hWWstar_def]; exact hh)
  have hWWstar_selfgen : pCentralGenerated p WWstar = WWstar := pCentralGenerated_idem WW
  -- |WW⋆| > |W| (W ⊊ WW⋆), contradicting maximality.
  have hW_lt_WWstar : W < WWstar := lt_of_le_of_ne hW_le_WWstar (Ne.symm hWWstar_ne_W)
  have hcard_gt : Nat.card W < Nat.card WWstar :=
    Set.Finite.card_lt_card (Set.toFinite _) (hW_lt_WWstar : (W : Set H) ⊂ _)
  have hle := hmaxW WWstar hWWstar_ne_bot hWWstar_p hWWstar_norm hWWstar_selfgen
  omega

/-- **§7D Step 5 (second half)** (Isaacs L4027-4030) — *a `p`-type maximal
subgroup contains no `q`-central element*.  **Now a theorem** (was an axiom),
proven from Step 4 (`step4_qCentral_normalizes_no_pCentral`, axiom) plus
Hall-Higman.

Stated symmetrically in `p, q` (apply with `p := q`, `q := p` and `hH_card` in
the swapped form to use the dual).

Proof: for `M` `p`-type, `V := O_p(M)` is a nontrivial `p`-subgroup with
`O_{p'}(M) = ⊥`.  `M = N_H(V)` (since `V` is characteristic in `M`, and by
maximality + simplicity).  Hall-Higman 1.2.3
(`centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot`) gives `C_M(V) ⊆ V`, so a
nontrivial central element of a Sylow `p`-subgroup `P_H ⊇ V` of `H` is a
`p`-central element lying in `V`.  A `q`-central `y ∈ M = N_H(V)` then
contradicts Step 4. -/
theorem step5b_pType_no_qCentral
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    {y : H} (hy_qcentral : IsPCentral q y) :
    y ∉ M := by
  classical
  intro hy_in_M
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- V := O_p(↥M) ≠ ⊥ (p-type); Vmap := V.map subtype.
  set K₀ : Subgroup ↥M := OddOrder.Isaacs.Ch01.opCore p ↥M with hK₀_def
  haveI hK₀_normal : K₀.Normal := by rw [hK₀_def]; infer_instance
  set V : Subgroup H := K₀.map M.subtype with hV_def
  have hV_ne_bot : V ≠ ⊥ := by
    intro hbot
    have hK₀_bot : K₀ = ⊥ := by
      rw [hV_def] at hbot
      exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hbot
    exact hM_pType.2 hK₀_bot
  have hV_le_M : V ≤ M := by rw [hV_def]; exact Subgroup.map_subtype_le _
  -- V is a p-group.
  have hV_pgroup : IsPGroup p V := by
    rw [hV_def]; exact (OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥M).map M.subtype
  -- M = N_H(V).
  have hM_norm_V : (M : Subgroup H) ≤ Subgroup.normalizer V := by
    have h1 : (Subgroup.normalizer (K₀ : Set ↥M)).map M.subtype
        ≤ Subgroup.normalizer ((K₀.map M.subtype : Subgroup H) : Set H) :=
      Subgroup.le_normalizer_map M.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hK₀_normal] at h1
    have h3 : (⊤ : Subgroup ↥M).map M.subtype = M := by
      rw [← MonoidHom.range_eq_map, M.range_subtype]
    rw [h3] at h1; rw [hV_def]; exact h1
  have hM_eq_NV : Subgroup.normalizer V = M :=
    maximal_eq_normalizer_of_M_normalizes hM_pType.1 hV_ne_bot hV_le_M hM_norm_V
  -- y ∈ M = N_H(V).
  have hy_norm : y ∈ Subgroup.normalizer V := hM_eq_NV ▸ hy_in_M
  -- A p-central element x ∈ V (via Z(P_H) + Hall-Higman in ↥M).
  -- (i) P_H ∈ Syl_p(H) with V ≤ P_H.
  obtain ⟨PH, hV_le_PH⟩ := IsPGroup.exists_le_sylow hV_pgroup
  have hPH_ne_bot : (PH : Subgroup H) ≠ ⊥ := Sylow.ne_bot_of_dvd_card hp_dvd PH
  -- (ii) nontrivial Z(P_H) element x, p-central.
  haveI : Nontrivial ↥(PH : Subgroup H) :=
    (PH : Subgroup H).nontrivial_iff_ne_bot.mpr hPH_ne_bot
  have hPHpg : IsPGroup p ↥(PH : Subgroup H) := PH.isPGroup'
  have hZPH_nt : Nontrivial (Subgroup.center ↥(PH : Subgroup H)) := hPHpg.center_nontrivial
  obtain ⟨⟨⟨x, hx_mem_PH⟩, hx_center⟩, hx_ne_one⟩ :=
    exists_ne (1 : Subgroup.center ↥(PH : Subgroup H))
  have hx_ne_one' : x ≠ 1 := by
    intro h1; apply hx_ne_one; apply Subtype.ext; apply Subtype.ext; exact h1
  have hx_pcentral : IsPCentral p x := ⟨hx_ne_one', PH, ⟨x, hx_mem_PH⟩, hx_center, rfl⟩
  -- (iii) x centralizes V (V ≤ P_H, x ∈ Z(P_H)).
  have hx_centralizes_V : x ∈ Subgroup.centralizer (V : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv_PH : v ∈ (PH : Subgroup H) := hV_le_PH hv
    have hcomm := (Subgroup.mem_center_iff.mp hx_center) ⟨v, hv_PH⟩
    have h2 := congrArg (Subgroup.subtype (PH : Subgroup H)) hcomm
    simpa using h2
  -- (iv) x ∈ N_H(V) = M.
  have hx_in_NV : x ∈ Subgroup.normalizer V := centralizer_le_normalizer V hx_centralizes_V
  have hx_in_M : x ∈ M := hM_eq_NV ▸ hx_in_NV
  -- (v) xM := ⟨x,_⟩ ∈ C_M(K₀) (Hall-Higman context). Then xM ∈ K₀ ⇒ x ∈ V.
  set xM : ↥M := ⟨x, hx_in_M⟩ with hxM_def
  have hxM_cent_K₀ : xM ∈ Subgroup.centralizer (K₀ : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    -- w ∈ K₀; ↑w ∈ V; x centralizes ↑w.
    have hw_V : (M.subtype w) ∈ V := by rw [hV_def]; exact ⟨w, hw, rfl⟩
    have hxc := (Subgroup.mem_centralizer_iff.mp hx_centralizes_V) (M.subtype w) hw_V
    -- hxc : M.subtype w * x = x * M.subtype w.  Lift to ↥M.
    apply M.subtype_injective
    simp only [Subgroup.coe_mul, Subgroup.coe_subtype, hxM_def]
    exact hxc
  -- Hall-Higman in ↥M: C_M(K₀) ⊆ K₀.
  haveI hM_pSep : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) ↥M := by
    have hM_ne_top : (M : Subgroup H) ≠ ⊤ := hM_pType.1.ne_top
    haveI hM_sol : IsSolvable ↥M := hSubgroupsSolvable M hM_ne_top
    infer_instance
  have hOpp' : OddOrder.Isaacs.Ch03.oPiCore {r | r ≠ p} ↥M = ⊥ :=
    oPiCore_pPrime_eq_bot_of_isPType hpq hH_card hSubgroupsSolvable hM_pType
  have hHH : Subgroup.centralizer (K₀ : Set ↥M) ≤ K₀ := by
    rw [hK₀_def]
    exact centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot hOpp'
  have hxM_in_K₀ : xM ∈ K₀ := hHH hxM_cent_K₀
  have hx_in_V : x ∈ V := by rw [hV_def]; exact ⟨xM, hxM_in_K₀, rfl⟩
  -- (vi) Step 4: y q-central ∈ N_H(V), V p-group, x p-central ∈ V ⇒ False.
  exact step4_qCentral_normalizes_no_pCentral hpq hH_card hH_nsol hSubgroupsSolvable
    hy_qcentral hV_pgroup hy_norm hx_pcentral hx_in_V

/-- **§7D Step 6** (Isaacs L4031-4037) — *a `q`-central element cannot normalize
a nontrivial `p`-subgroup*.

**Proven** from Step 5 (second half) + the landed
`exists_isPCentral_centralizing` and the dichotomy.

Proof (textbook): let `V` be a nontrivial `p`-subgroup and `M ⊇ N_G(V)` a
maximal subgroup.  `N_G(V)` contains a `p`-central element (`Z(P) ⊆ C_G(V) ⊆
N_G(V)`), so `M` does too; by Step 5 (second half, with `p, q` swapped) `M`
cannot be `q`-type, hence `M` is `p`-type.  Then by Step 5 (second half) `M`
contains no `q`-central element.  In particular a `q`-central `y ∈ N_G(V) ⊆ M`
is impossible. -/
theorem step6_qCentral_not_normalizes_nontrivial_pSubgroup
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {y : H} (hy_qcentral : IsPCentral q y)
    {V : Subgroup H} (hV_ne_bot : V ≠ ⊥) (hV_pgroup : IsPGroup p V)
    (hy_norm : y ∈ Subgroup.normalizer V) :
    False := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  -- p ∣ |H| and q ∣ |H| (so p-central elements exist).
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- A maximal subgroup M ⊇ N_G(V).
  have hNV_ne_top : Subgroup.normalizer (V : Set H) ≠ ⊤ := by
    -- If N_G(V) = ⊤ then V ⊴ H, so V ∈ {⊥, ⊤} by simplicity; V ≠ ⊥, and V = ⊤
    -- would make H a p-group (V ≤ H p-subgroup), contradicting q ∣ |H|.
    intro hNV_top
    have hV_normal : V.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]; exact hNV_top
    rcases hV_normal.eq_bot_or_eq_top with hbot | htop
    · exact hV_ne_bot hbot
    · -- V = ⊤ ⇒ H is a p-group ⇒ q ∤ |H|, contradiction.
      have hH_pgroup : IsPGroup p H := by
        have : IsPGroup p (⊤ : Subgroup H) := htop ▸ hV_pgroup
        exact (this.of_equiv Subgroup.topEquiv)
      obtain ⟨k, hk⟩ := hH_pgroup.exists_card_eq
      rw [hk] at hq_dvd
      have : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp
        (hq_prime.dvd_of_dvd_pow hq_dvd)
      exact hpq this.symm
  obtain ⟨M, hM_max, hNV_le⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom
      (Subgroup.normalizer (V : Set H))).resolve_left hNV_ne_top
  -- N_G(V) contains a p-central element (centralizing V).
  obtain ⟨x, hx_pcentral, hx_comm⟩ := exists_isPCentral_centralizing hp_dvd V hV_pgroup
  have hx_in_CV : x ∈ Subgroup.centralizer (V : Set H) := by
    rw [Subgroup.mem_centralizer_iff]; intro v hv; exact (hx_comm v hv).symm
  have hx_in_NV : x ∈ Subgroup.normalizer V := centralizer_le_normalizer V hx_in_CV
  have hx_in_M : x ∈ M := hNV_le hx_in_NV
  -- M is p-type: it is not q-type, since a q-type maximal contains no
  -- p-central element (Step 5b with p,q swapped), but x ∈ M is p-central.
  have hM_ne_bot : M ≠ ⊥ := by
    intro hbot; rw [hbot] at hx_in_M
    exact hx_pcentral.ne_one (Subgroup.mem_bot.mp hx_in_M)
  have hM_pType : IsPType p M := by
    rcases maximal_isPType_xor_isQType hpq hH_card hSubgroupsSolvable hM_max hM_ne_bot with
      h | h
    · exact h.1
    · -- M is q-type: then by Step 5b (swapped) no p-central element ∈ M,
      -- contradicting x ∈ M being p-central.
      exfalso
      exact step5b_pType_no_qCentral (Ne.symm hpq) (a := b) (b := a)
        (by rw [hH_card]; ring) hH_nsol hSubgroupsSolvable h.1 hx_pcentral hx_in_M
  -- y is q-central and ∈ N_G(V) ⊆ M; Step 5b (p-type, no q-central) ⇒ False.
  have hy_in_M : y ∈ M := hNV_le hy_norm
  exact step5b_pType_no_qCentral hpq hH_card hH_nsol hSubgroupsSolvable hM_pType hy_qcentral hy_in_M

/-- **§7D Step 7** (Isaacs L4039-4043) — *both primes are odd*.

If `q = 2`, choose an involution `t` in the center of a Sylow `2`-subgroup
(so `t` is `q`-central).  By Matsuyama (Thm 2.13) there is an element `x` of odd
prime order with `t x t = x⁻¹`, hence `t ∈ N_G(⟨x⟩)` where `⟨x⟩` is a nontrivial
`p`-subgroup.  This contradicts Step 6.  Symmetrically `p ≠ 2`.

This step is **proven** from the Step 6 axiom and the landed
`matsuyama_of_simple_nonsolvable_q_two`. -/
theorem step7_p_ne_two_and_q_ne_two
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K) :
    p ≠ 2 ∧ q ≠ 2 := by
  classical
  -- The two cases are symmetric (swap p,q).  We prove a uniform sub-claim:
  -- if r is one of the two primes with r = 2 and s is the other prime (odd,
  -- s ∣ |H|), then we reach a contradiction with Step 6.
  -- Sub-claim: for primes r, s with r ≠ s, |H| = r^m s^k decomposition, r = 2,
  -- and Step 6 available for s-central elements normalizing r... but Step 6 is
  -- stated for q-central elements normalizing p-subgroups.  We need r playing
  -- the q-role and s playing the p-role.  Instantiate Step 6 accordingly.
  have key : ∀ (r s : ℕ) [Fact r.Prime] [Fact s.Prime], r ≠ s →
      ∀ m k : ℕ, Nat.card H = s ^ m * r ^ k → r = 2 → False := by
    intro r s _ _ hrs m k hcard hr2
    subst hr2
    -- A 2-central involution t exists: pick Q ∈ Syl_2, Z(Q) nontrivial 2-group.
    have h2_dvd : (2 : ℕ) ∣ Nat.card H :=
      (p_and_q_dvd_card_of_simple_nonsolvable (Ne.symm hrs) inferInstance hH_nsol
        (dvd_of_eq hcard)).2
    -- Build the 2-central involution.
    obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := H)
    have hQ_ne_bot : (Q : Subgroup H) ≠ ⊥ := Sylow.ne_bot_of_dvd_card h2_dvd Q
    haveI : Nontrivial ↥(Q : Subgroup H) :=
      (Q : Subgroup H).nontrivial_iff_ne_bot.mpr hQ_ne_bot
    have hQpg : IsPGroup 2 ↥(Q : Subgroup H) := Q.isPGroup'
    have hZ_nt : Nontrivial (Subgroup.center ↥(Q : Subgroup H)) := hQpg.center_nontrivial
    -- 2 ∣ |Z(Q)| (nontrivial 2-group center), so Z(Q) has an involution.
    have h2_dvd_Z : (2 : ℕ) ∣ Nat.card (Subgroup.center ↥(Q : Subgroup H)) := by
      have hZpg : IsPGroup 2 (Subgroup.center ↥(Q : Subgroup H)) :=
        hQpg.to_subgroup _
      obtain ⟨k, hk⟩ := hZpg.exists_card_eq
      rw [hk]
      have hk_pos : 0 < k := by
        by_contra hk0
        rw [Nat.eq_zero_of_not_pos hk0, pow_zero] at hk
        exact (Finite.one_lt_card (α := Subgroup.center ↥(Q : Subgroup H))).ne' hk
      exact dvd_pow_self 2 hk_pos.ne'
    obtain ⟨z, hz_ord⟩ := exists_prime_orderOf_dvd_card' 2 h2_dvd_Z
    -- z ∈ Z(Q) with order 2; lift to t ∈ H, an involution, 2-central.
    -- z : ↥(center ↥↑Q).  The Sylow element is (z : ↥↑Q), and t = ((z : ↥↑Q) : H).
    set zQ : ↥(Q : Subgroup H) := (z : ↥(Q : Subgroup H)) with hzQ_def
    set t : H := (zQ : H) with ht_def
    -- orderOf t = orderOf zQ = orderOf z = 2.
    have ht_ord : orderOf t = 2 := by
      rw [ht_def, Subgroup.orderOf_coe, hzQ_def, Subgroup.orderOf_coe, hz_ord]
    have ht_ne_one : t ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at ht_ord
      exact (by norm_num : (1 : ℕ) ≠ 2) ht_ord
    have ht_sq : t * t = 1 := by
      have ht2 : t ^ 2 = 1 := by
        rw [← ht_ord]; exact pow_orderOf_eq_one t
      rw [pow_two] at ht2; exact ht2
    -- Matsuyama: ∃ x of odd prime order with t x t = x⁻¹.
    obtain ⟨x, p₀, hp₀_prime, hp₀_odd, hx_ord, hxt⟩ :=
      matsuyama_of_simple_nonsolvable_q_two inferInstance hH_nsol ht_sq ht_ne_one
    -- t normalizes ⟨x⟩.
    have hx_ne_one : x ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hx_ord
      exact hp₀_prime.ne_one hx_ord.symm
    -- ⟨x⟩ is a p₀-subgroup; p₀ is odd and divides |H| = s^a 2^b, so p₀ = s.
    have hp₀_dvd : p₀ ∣ Nat.card H := hx_ord ▸ orderOf_dvd_natCard x
    have hp₀_eq_s : p₀ = s := by
      rw [hcard] at hp₀_dvd
      rcases (Nat.Prime.dvd_mul hp₀_prime).mp hp₀_dvd with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hp₀_prime (Fact.out (p := s.Prime))).mp
          (hp₀_prime.dvd_of_dvd_pow h)
      · -- p₀ ∣ 2^b ⇒ p₀ = 2, contradicting p₀ odd.
        exfalso
        have : p₀ = 2 := (Nat.prime_dvd_prime_iff_eq hp₀_prime Nat.prime_two).mp
          (hp₀_prime.dvd_of_dvd_pow h)
        rw [this] at hp₀_odd
        exact (by decide : ¬ Odd 2) hp₀_odd
    -- t is 2-central, i.e. q-central with q := 2.  ⟨x⟩ is a nontrivial
    -- s-subgroup.  Apply Step 6 with (p := s, q := 2).
    haveI : Fact s.Prime := inferInstance
    -- t is 2-central: t = (zQ : H), zQ = (z : ↥↑Q) ∈ center ↥↑Q.
    have ht_2central : IsPCentral 2 t :=
      ⟨ht_ne_one, Q, zQ, z.2, rfl⟩
    -- ⟨x⟩ s-subgroup, nontrivial.
    have hX_pgroup : IsPGroup s (Subgroup.zpowers x) := by
      rw [← hp₀_eq_s]
      apply IsPGroup.of_card (n := 1)
      rw [pow_one, Nat.card_zpowers, hx_ord]
    have hX_ne_bot : Subgroup.zpowers x ≠ ⊥ :=
      fun h => hx_ne_one (Subgroup.zpowers_eq_bot.mp h)
    -- t normalizes ⟨x⟩: conjugation by t (= t⁻¹) sends x ↦ t x t⁻¹ = t x t = x⁻¹,
    -- so it maps ⟨x⟩ into ⟨x⁻¹⟩ = ⟨x⟩, and likewise the reverse.
    have ht_inv : t⁻¹ = t := by
      rw [inv_eq_iff_mul_eq_one]; exact ht_sq
    -- t x t⁻¹ = x⁻¹.
    have hconj : t * x * t⁻¹ = x⁻¹ := by rw [ht_inv]; exact hxt
    -- x⁻¹ ∈ ⟨x⟩, hence (x⁻¹)^k ∈ ⟨x⟩ for all k.
    have hxinv_mem : ∀ k : ℤ, (x⁻¹) ^ k ∈ Subgroup.zpowers x := fun k =>
      (Subgroup.zpowers x).zpow_mem ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)) k
    have ht_norm : t ∈ Subgroup.normalizer (Subgroup.zpowers x) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨fun hw => ?_, fun hw => ?_⟩
      · -- w ∈ ⟨x⟩ ⇒ t w t⁻¹ ∈ ⟨x⟩.
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        have h2 : t * x ^ k * t⁻¹ = (x⁻¹) ^ k := by
          rw [← conj_zpow (a := t) (b := x) (i := k), hconj]
        rw [h2]; exact hxinv_mem k
      · -- t w t⁻¹ ∈ ⟨x⟩ ⇒ w ∈ ⟨x⟩, via w = t⁻¹ (t w t⁻¹) t = t (t w t⁻¹) t⁻¹.
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
        -- t w t⁻¹ = x^k ⇒ w = t⁻¹ x^k t.  With t⁻¹ = t: w = t x^k t⁻¹ = (x⁻¹)^k.
        have hw_eq : w = t * x ^ k * t⁻¹ := by
          have : t * w * t⁻¹ = x ^ k := hk.symm
          calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
            _ = t * (t * w * t⁻¹) * t⁻¹ := by rw [ht_inv]
            _ = t * x ^ k * t⁻¹ := by rw [this]
        have h3 : t * x ^ k * t⁻¹ = (x⁻¹) ^ k := by
          rw [← conj_zpow (a := t) (b := x) (i := k), hconj]
        rw [hw_eq, h3]; exact hxinv_mem k
    exact step6_qCentral_not_normalizes_nontrivial_pSubgroup (p := s) (q := 2)
      (Ne.symm hrs) hcard hH_nsol hSubgroupsSolvable ht_2central hX_ne_bot hX_pgroup ht_norm
  refine ⟨?_, ?_⟩
  · -- p = 2: instantiate key with r := p (= 2), s := q.  |H| = q^b * p^a.
    intro hp2
    exact key p q hpq b a (by rw [hH_card]; ring) hp2
  · -- q = 2: instantiate key with r := q (= 2), s := p.  |H| = p^a * q^b = hH_card.
    intro hq2
    exact key q p (Ne.symm hpq) a b hH_card hq2

end OddOrder.Isaacs.Ch07
