/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7D1_BurnsideSetup

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
Import chain: S7A1 → S7A2 → S7B1 → S7B2 → S7D1 → Main.

* `S7A1_JpGL2p` — §7A part 1 (J(P), Thm 7.1 stmt, Lem 7.3 GL(2,p))
* `S7A2_NormalPThm75` — §7A part 2 (Lem 7.3 formal, Thm 7.5, action infra)
* `S7B1_NormalJ` — §7B Steps 1-6
* `S7B2_NormalJ_PComplement` — §7B close + §7C (Thm 7.1 proof, Thm 7.7)
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

/-- **§7D helper** — normalizer-grows. If `D < ↑S` for a finite `p`-group Sylow `S`,
then `D` is strictly contained in `N_H(D) ⊓ ↑S`. -/
theorem lt_normalizer_inf_sylow_of_lt
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (S : Sylow p H) {D : Subgroup H} (hD_lt : D < (S : Subgroup H)) :
    D < Subgroup.normalizer D ⊓ (S : Subgroup H) := by
  classical
  haveI : Group.IsNilpotent ↥(S : Subgroup H) := S.isPGroup'.isNilpotent
  have hNC : NormalizerCondition ↥(S : Subgroup H) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup H))
  -- D.subgroupOf S < ⊤.
  have hD_le : D ≤ (S : Subgroup H) := le_of_lt hD_lt
  have hsub_lt_top : D.subgroupOf (S : Subgroup H) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact (ne_of_lt hD_lt) (le_antisymm hD_le htop)
  have hlt := hNC (D.subgroupOf (S : Subgroup H)) hsub_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hD_le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  -- ↑t ∈ N_H(D) ⊓ ↑S, ↑t ∉ D.
  refine lt_of_le_of_ne (le_inf ?_ hD_le) ?_
  · -- D ≤ N_H(D).
    exact Subgroup.le_normalizer
  · intro heq
    apply ht_not
    have : (t : H) ∈ Subgroup.normalizer D ⊓ (S : Subgroup H) := ⟨ht_norm, t.2⟩
    rw [← heq] at this
    exact this

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
      show g⁻¹ * (MulAut.conj g m) * g ∈ M
      rw [MulAut.conj_apply, show g⁻¹ * (g * m * g⁻¹) * g = m from by group]
      exact hm
    · intro hx
      refine ⟨g⁻¹ * x * g, hx, ?_⟩
      show MulAut.conj g (g⁻¹ * x * g) = x
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

/-! ### §7D Step 8 — normal `J` for `p`-type maximals (Isaacs L4045-4063)

Helper lemmas toward discharging Step 8 (the `normal_J` hypotheses for `M`). -/


/-- **§7D Step 8 helper** — `2 ∤ |M|` for a subgroup `M` of a simple `p^a q^b`
group with `p, q` both odd.  Hence Sylow-`2` subgroups of `M` are trivial. -/
theorem two_not_dvd_card_subgroup_of_odd_primes
    {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (_hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (M : Subgroup H) :
    ¬ (2 : ℕ) ∣ Nat.card ↥M := by
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  intro h2_dvd
  have h2_dvd_H : (2 : ℕ) ∣ Nat.card H := h2_dvd.trans M.card_subgroup_dvd_card
  rw [hH_card] at h2_dvd_H
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2_dvd_H with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp_prime).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq_prime).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm

/-- **§7D Step 8 helper** — Sylow-`2` subgroups of `M` are abelian (in fact
trivial) when `2 ∤ |M|`.  Phrased as the `normal_J` hypothesis. -/
theorem sylow2_abelian_of_two_not_dvd
    {M : Type*} [Group M] [Finite M]
    (h2 : ¬ (2 : ℕ) ∣ Nat.card M) :
    ∀ S : Subgroup M, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS x y
  -- `S` is a `2`-group; `|S| ∣ |M|`; since `2 ∤ |M|`, `|S| = 1`, so `S` is trivial.
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hS_dvd : Nat.card ↥S ∣ Nat.card M := S.card_subgroup_dvd_card
  have hn0 : n = 0 := by
    by_contra hne
    exact h2 ((hn ▸ dvd_pow_self 2 hne).trans hS_dvd)
  have hS_card_one : Nat.card ↥S = 1 := by rw [hn, hn0, pow_zero]
  haveI : Subsingleton ↥S := Nat.card_eq_one_iff_unique.mp hS_card_one |>.1
  exact Subsingleton.elim (x * y) (y * x)

/-- **§7D Step 8 — fifth normal-J hypothesis** (Isaacs L4055-4063): for a
`p`-type maximal `M` and `S ∈ Syl_p(M)`, the centralizer of `Z(S)` in `M`
is exactly `S`: `C_M(Z(S)) = S`.

Textbook proof: `S ⊆ C_M(Z(S))` always.  For the reverse it suffices that
`C_M(Z(S))` is a `p`-group (a `p`-subgroup of `M` containing the Sylow `S` must
equal `S`).  Otherwise an order-`q` element `y ∈ C_M(Z(S))` gives a nontrivial
`q`-subgroup `Y = ⟨y⟩` normalized by `Z(S)`; choosing `P ∈ Syl_p(H)` with
`S = M ∩ P` and `M = N_H(O_p(M))`, the nontrivial center `Z(P)` lies in
`M ∩ P = S` and centralizes `S`, hence `Z(S)` contains a `p`-central element `x`
of `H`.  Then `x` normalizes `Y`, contradicting Step 6 (with `p, q` swapped). -/
theorem step8_centralizer_center_eq_sylow
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    (S : Sylow p ↥M) :
    Subgroup.centralizer
      (((Subgroup.center (S : Subgroup ↥M)).map (S : Subgroup ↥M).subtype) : Set ↥M)
      = (S : Subgroup ↥M) := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  -- `p ∣ |H|`, `q ∣ |H|`.
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- Abbreviations.
  set ZS : Subgroup ↥M :=
    (Subgroup.center (S : Subgroup ↥M)).map (S : Subgroup ↥M).subtype with hZS_def
  set C : Subgroup ↥M := Subgroup.centralizer (ZS : Set ↥M) with hC_def
  -- (A) `S ≤ C_M(Z(S))`: every `s ∈ S` commutes with `Z(S)`.
  have hS_le_C : (S : Subgroup ↥M) ≤ C := by
    intro s hs
    rw [hC_def, Subgroup.mem_centralizer_iff]
    intro z hz
    -- `z ∈ Z(S).map subtype`: `z = ↑z₀` with `z₀ ∈ center S`.
    obtain ⟨z₀, hz₀_center, rfl⟩ := hz
    -- `z₀` central in `S` ⇒ commutes with `⟨s, hs⟩`.
    have := (Subgroup.mem_center_iff.mp hz₀_center) ⟨s, hs⟩
    -- push to `↥M`.
    have h2 := congrArg (Subgroup.subtype (S : Subgroup ↥M)) this
    simpa [mul_comm] using h2.symm
  -- (B) `C` is a `p`-group.  Suppose not, and derive a contradiction via Step 6.
  have hC_pgroup : IsPGroup p C := by
    by_contra hC_not_p
    -- `q ∣ |C|`: a prime `r ∣ |C|` with `r ≠ p` must be `q` (since `|C| ∣ |M| ∣ p^a q^b`).
    -- Some prime `r ∣ |C|` is `≠ p` (else `C` would be a `p`-group).
    have hq_dvd_C : q ∣ Nat.card ↥C := by
      by_contra hq_ndvd
      -- Every prime factor of `|C|` is `p`, so `C` is a `p`-group — contradiction.
      apply hC_not_p
      apply OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton (G := ↥M) (p := p)
      intro r hr
      obtain ⟨hr_prime, hr_dvd_C, _⟩ := Nat.mem_primeFactors.mp hr
      have hr_dvd_M : r ∣ Nat.card ↥M := hr_dvd_C.trans C.card_subgroup_dvd_card
      have hr_dvd_paqb : r ∣ p ^ a * q ^ b := by
        rw [← hH_card]; exact hr_dvd_M.trans M.card_subgroup_dvd_card
      simp only [Set.mem_singleton_iff]
      rcases (Nat.Prime.dvd_mul hr_prime).mp hr_dvd_paqb with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp (hr_prime.dvd_of_dvd_pow h)
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp
          (hr_prime.dvd_of_dvd_pow h) ▸ hr_dvd_C) hq_ndvd
    -- Cauchy: an order-`q` element `y₀ ∈ C`.
    haveI : Fact q.Prime := ⟨hq_prime⟩
    obtain ⟨y₀, hy₀_ord⟩ := exists_prime_orderOf_dvd_card' q hq_dvd_C
    -- `Y₀ = ⟨y₀.val⟩` is a nontrivial `q`-subgroup of `↥M`; map to `H`.
    set yM : ↥M := (y₀ : ↥M) with hyM_def
    have hyM_ord : orderOf yM = q := by rw [hyM_def, Subgroup.orderOf_coe, hy₀_ord]
    have hyM_ne_one : yM ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hyM_ord; exact hq_prime.ne_one hyM_ord.symm
    set Y₀ : Subgroup ↥M := Subgroup.zpowers yM with hY₀_def
    have hY₀_q : IsPGroup q Y₀ := by
      apply IsPGroup.of_card (n := 1)
      rw [pow_one, hY₀_def, Nat.card_zpowers, hyM_ord]
    set YH : Subgroup H := Y₀.map M.subtype with hYH_def
    have hYH_q : IsPGroup q YH := hY₀_q.map M.subtype
    -- `YH ≠ ⊥` (since `yM ≠ 1` maps to `↑yM ≠ 1`).
    have hYH_ne_bot : YH ≠ ⊥ := by
      rw [hYH_def, hY₀_def]
      intro hbot
      apply hyM_ne_one
      have : (M.subtype yM) = 1 := by
        have hmem : M.subtype yM ∈ (Subgroup.zpowers yM).map M.subtype :=
          ⟨yM, Subgroup.mem_zpowers yM, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem; exact hmem
      simpa using this
    -- Build the ambient `p`-central element `x ∈ Z(S) ⊆ M ∩ P` normalizing `YH`.
    -- (i) `M = N_H(V)` for `V = O_p(M).map subtype`.
    set K₀ : Subgroup ↥M := OddOrder.Isaacs.Ch01.opCore p ↥M with hK₀_def
    haveI hK₀_normal : K₀.Normal := by rw [hK₀_def]; infer_instance
    set V : Subgroup H := K₀.map M.subtype with hV_def
    have hV_ne_bot : V ≠ ⊥ := by
      intro hbot
      -- `V = ⊥` and `subtype` injective ⇒ `K₀ = ⊥`, contradicting `IsPType`.
      have hK₀_bot : K₀ = ⊥ := by
        rw [hV_def] at hbot
        exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hbot
      exact hM_pType.2 hK₀_bot
    have hV_le_M : V ≤ M := by rw [hV_def]; exact Subgroup.map_subtype_le _
    have hM_norm_V : (M : Subgroup H) ≤ Subgroup.normalizer V := by
      -- `K₀ ⊴ ↥M` ⇒ `normalizer K₀ = ⊤`; map by `subtype` lands in `normalizer V`.
      have h1 : (Subgroup.normalizer (K₀ : Set ↥M)).map M.subtype
          ≤ Subgroup.normalizer ((K₀.map M.subtype : Subgroup H) : Set H) :=
        Subgroup.le_normalizer_map M.subtype
      rw [Subgroup.normalizer_eq_top_iff.mpr hK₀_normal] at h1
      have h3 : (⊤ : Subgroup ↥M).map M.subtype = M := by
        rw [← MonoidHom.range_eq_map, M.range_subtype]
      rw [h3] at h1
      rw [hV_def]
      exact h1
    have hM_eq_NV : Subgroup.normalizer V = M :=
      maximal_eq_normalizer_of_M_normalizes hM_pType.1 hV_ne_bot hV_le_M hM_norm_V
    -- (ii) `S_H := S.map subtype` extends to `P_H ∈ Syl_p(H)`.
    set SH : Subgroup H := (S : Subgroup ↥M).map M.subtype with hSH_def
    have hSH_p : IsPGroup p SH := S.isPGroup'.map M.subtype
    obtain ⟨PH, hSH_le_PH⟩ := IsPGroup.exists_le_sylow hSH_p
    have hPH_ne_bot : (PH : Subgroup H) ≠ ⊥ := Sylow.ne_bot_of_dvd_card hp_dvd PH
    -- (iii) `V ≤ SH ≤ PH` (since `K₀ = O_p(↥M) ≤ S`).
    have hV_le_SH : V ≤ SH := by
      rw [hV_def, hSH_def]
      exact Subgroup.map_mono (hK₀_def ▸ OddOrder.Isaacs.Ch01.opCore_le S)
    have hV_le_PH : V ≤ (PH : Subgroup H) := hV_le_SH.trans hSH_le_PH
    -- (iv) Nontrivial `Z(PH)` element `x`, `p`-central.
    haveI : Nontrivial ↥(PH : Subgroup H) :=
      (PH : Subgroup H).nontrivial_iff_ne_bot.mpr hPH_ne_bot
    have hPHpg : IsPGroup p ↥(PH : Subgroup H) := PH.isPGroup'
    have hZPH_nt : Nontrivial (Subgroup.center ↥(PH : Subgroup H)) := hPHpg.center_nontrivial
    obtain ⟨⟨⟨x, hx_mem_PH⟩, hx_center⟩, hx_ne_one⟩ :=
      exists_ne (1 : Subgroup.center ↥(PH : Subgroup H))
    have hx_ne_one' : x ≠ 1 := by
      intro h1; apply hx_ne_one; apply Subtype.ext; apply Subtype.ext; exact h1
    have hx_pcentral : IsPCentral p x := ⟨hx_ne_one', PH, ⟨x, hx_mem_PH⟩, hx_center, rfl⟩
    -- (v) `x ∈ M` (since `x ∈ Z(PH) ⊆ C_H(V) ⊆ N_H(V) = M`).
    have hx_centralizes_V : x ∈ Subgroup.centralizer (V : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv_PH : v ∈ (PH : Subgroup H) := hV_le_PH hv
      have hcomm := (Subgroup.mem_center_iff.mp hx_center) ⟨v, hv_PH⟩
      have := congrArg (Subgroup.subtype (PH : Subgroup H)) hcomm
      simpa [Subgroup.coe_mul] using this
    have hx_in_NV : x ∈ Subgroup.normalizer V := centralizer_le_normalizer V hx_centralizes_V
    have hx_in_M : x ∈ M := hM_eq_NV ▸ hx_in_NV
    -- (vi) `S = PH.subgroupOf M` (a `p`-subgroup of `↥M` containing the Sylow `S`).
    set xM : ↥M := ⟨x, hx_in_M⟩ with hxM_def
    have hPH_subOf_p : IsPGroup p ((PH : Subgroup H).subgroupOf M) :=
      hPHpg.comap_subtype
    have hS_le_PH_subOf : (S : Subgroup ↥M) ≤ (PH : Subgroup H).subgroupOf M := by
      intro s hs
      -- `↑s ∈ SH ≤ PH`.
      have : M.subtype s ∈ SH := ⟨s, hs, rfl⟩
      exact hSH_le_PH this
    have hS_eq : (PH : Subgroup H).subgroupOf M = (S : Subgroup ↥M) :=
      S.is_maximal' hPH_subOf_p hS_le_PH_subOf
    -- `xM ∈ S` since `↑xM = x ∈ PH`, i.e. `xM ∈ PH.subgroupOf M = S`.
    have hxM_in_S : xM ∈ (S : Subgroup ↥M) := by
      rw [← hS_eq, Subgroup.mem_subgroupOf]; exact hx_mem_PH
    -- (vii) `xM ∈ Z(S)`: `xM` centralizes `S` because `x ∈ Z(PH)` centralizes `PH ⊇ SH`.
    have hxM_center_S : (⟨xM, hxM_in_S⟩ : ↥(S : Subgroup ↥M)) ∈
        Subgroup.center (S : Subgroup ↥M) := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      apply Subtype.ext
      -- Reduce to commutation in `H`: `x * ↑s = ↑s * x`.
      have hs_PH : M.subtype (s : ↥M) ∈ (PH : Subgroup H) := by
        have : M.subtype (s : ↥M) ∈ SH := ⟨(s : ↥M), s.2, rfl⟩
        exact hSH_le_PH this
      have hcomm := (Subgroup.mem_center_iff.mp hx_center) ⟨M.subtype (s : ↥M), hs_PH⟩
      have hcomm' := congrArg (Subgroup.subtype (PH : Subgroup H)) hcomm
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at hcomm'
      -- `hcomm' : x * ↑s = ↑s * x`; goal is `↑s * x = x * ↑s`.
      simpa [Subgroup.coe_mul, hxM_def] using hcomm'
    have hxM_in_ZS : xM ∈ ZS :=
      ⟨⟨xM, hxM_in_S⟩, hxM_center_S, rfl⟩
    -- (viii) `xM` centralizes `yM` (since `yM ∈ C = C_M(Z(S))` and `xM ∈ Z(S)`).
    have hyM_in_C : yM ∈ C := y₀.2
    have hxM_comm_yM : x * M.subtype yM = M.subtype yM * x := by
      rw [hC_def, Subgroup.mem_centralizer_iff] at hyM_in_C
      have hcomm := hyM_in_C xM hxM_in_ZS
      -- `hcomm : xM * yM = yM * xM` in `↥M`; push to `H`.
      have := congrArg (Subgroup.subtype M) hcomm
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at this
      -- `↑xM = x`.
      simpa [hxM_def] using this
    -- (ix) `x` centralizes `↑yM`, hence `x ∈ N_H(YH)`.
    have hx_norm_YH : x ∈ Subgroup.normalizer YH := by
      apply centralizer_le_normalizer YH
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [hYH_def] at hw
      obtain ⟨w₀, hw₀_mem, rfl⟩ := hw
      -- `w₀ ∈ ⟨yM⟩`, so `w₀ = yM ^ k`; `x` commutes with `↑yM` ⇒ with `↑w₀`.
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw₀_mem
      -- `M.subtype (yM ^ k) = (M.subtype yM) ^ k`; `x` commutes with `M.subtype yM`.
      rw [map_zpow]
      -- goal: `(M.subtype yM)^k * x = x * (M.subtype yM)^k`.
      have hcx : Commute x (M.subtype yM) := hxM_comm_yM
      exact (hcx.zpow_right k).symm
    -- (x) Step 6 swapped: `x` `p`-central normalizing nontrivial `q`-subgroup `YH` ⇒ False.
    exact step6_qCentral_not_normalizes_nontrivial_pSubgroup (p := q) (q := p) (a := b) (b := a)
      (Ne.symm hpq) (by rw [hH_card]; ring) hH_nsol hSubgroupsSolvable hx_pcentral
      hYH_ne_bot hYH_q hx_norm_YH
  -- (C) `C` is a `p`-subgroup of `↥M` containing the Sylow `S`, hence `C = S`.
  exact S.is_maximal' hC_pgroup hS_le_C

/-- **§7D Step 8 — full Sylow** (Isaacs L4060-4063): for a `p`-type maximal `M`
and `S ∈ Syl_p(M)`, the image `S.map subtype` is a *full* Sylow `p`-subgroup of
the ambient group `H`.

Textbook proof: by the first part of Step 8, `J(S) ⊴ M`, and since `M` is
maximal with `J(S) ≤ M` nontrivial and `M`-normalized, `N_H(J(S)) = M`.  If
`S_H := S.map subtype` were not a full Sylow of `H`, then `S_H < T` for a
`p`-subgroup `T` (take `T = N_{P_H}(S_H)` for `P_H ∈ Syl_p(H)` containing `S_H`,
which strictly contains `S_H` by the normalizer condition for the nilpotent
group `P_H`); as `J(S_H)` is characteristic in `S_H`, `T` normalizes `J(S_H)`,
so `T ⊆ N_H(J(S_H)) = M`, making `T` a `p`-subgroup of `M` containing the Sylow
`S = M ∩ P_H` — but `T > S_H`, contradiction.  Hence `S_H = P_H` is a full
Sylow. -/
theorem step8_sylow_full
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (_hpq : p ≠ q)
    {a b : ℕ} (_hH_card : Nat.card H = p ^ a * q ^ b)
    (_hH_nsol : ¬ IsSolvable H)
    (_hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    (S : Sylow p ↥M)
    (hJ_normal : (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal) :
    ((S : Subgroup ↥M).map M.subtype) ∈
      Set.range (fun P : Sylow p H => (P : Subgroup H)) := by
  classical
  have hp_prime : p.Prime := Fact.out
  -- `M ≠ ⊥`; `O_p(↥M) ≠ ⊥`.
  have hOp_ne_bot : OddOrder.Isaacs.Ch01.opCore p ↥M ≠ ⊥ := hM_pType.2
  -- `SH := S.map subtype`, a `p`-group; extend to `PH ∈ Syl_p(H)`.
  set SH : Subgroup H := (S : Subgroup ↥M).map M.subtype with hSH_def
  have hSH_p : IsPGroup p SH := S.isPGroup'.map M.subtype
  obtain ⟨PH, hSH_le_PH⟩ := IsPGroup.exists_le_sylow hSH_p
  -- `SH ≠ ⊥` (since `O_p(↥M) ≤ S`, `O_p(↥M).map subtype ≤ SH` nontrivial).
  have hSH_ne_bot : SH ≠ ⊥ := by
    rw [hSH_def]
    intro hbot
    apply hOp_ne_bot
    have hOp_le_S : OddOrder.Isaacs.Ch01.opCore p ↥M ≤ (S : Subgroup ↥M) :=
      OddOrder.Isaacs.Ch01.opCore_le S
    have : (OddOrder.Isaacs.Ch01.opCore p ↥M).map M.subtype = ⊥ :=
      le_bot_iff.mp ((Subgroup.map_mono hOp_le_S).trans (le_of_eq hbot))
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp this
  -- `J(SH) = (J S).map subtype`.
  have hJSH : Subgroup.thompsonJ SH p = (Subgroup.thompsonJ (S : Subgroup ↥M) p).map M.subtype :=
    Subgroup.thompsonJ_map_of_injective M.subtype_injective (S : Subgroup ↥M) p
  -- `J(SH) ≠ ⊥`, `J(SH) ≤ M`.
  have hJSH_ne_bot : Subgroup.thompsonJ SH p ≠ ⊥ := Subgroup.thompsonJ_ne_bot hSH_p hSH_ne_bot
  have hJSH_le_M : Subgroup.thompsonJ SH p ≤ M :=
    (Subgroup.thompsonJ_le SH p).trans (hSH_def ▸ Subgroup.map_subtype_le _)
  -- `M ≤ N_H(J(SH))` from `J(S) ⊴ M` (the image is M-conjugation-invariant).
  have hM_norm_JSH : (M : Subgroup H) ≤ Subgroup.normalizer (Subgroup.thompsonJ SH p) := by
    have h1 : (Subgroup.normalizer (Subgroup.thompsonJ (S : Subgroup ↥M) p)).map M.subtype
        ≤ Subgroup.normalizer ((Subgroup.thompsonJ (S : Subgroup ↥M) p).map M.subtype) :=
      Subgroup.le_normalizer_map M.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hJ_normal] at h1
    have h3 : (⊤ : Subgroup ↥M).map M.subtype = M := by
      rw [← MonoidHom.range_eq_map, M.range_subtype]
    rw [h3] at h1
    rw [hJSH]; exact h1
  -- `N_H(J(SH)) = M` (maximality).
  have hNJSH_eq_M : Subgroup.normalizer (Subgroup.thompsonJ SH p) = M :=
    maximal_eq_normalizer_of_M_normalizes hM_pType.1 hJSH_ne_bot hJSH_le_M hM_norm_JSH
  -- `S = PH.subgroupOf M`, i.e. `SH = M ⊓ PH`.
  have hPH_subOf_p : IsPGroup p ((PH : Subgroup H).subgroupOf M) := PH.isPGroup'.comap_subtype
  have hS_le_PH_subOf : (S : Subgroup ↥M) ≤ (PH : Subgroup H).subgroupOf M := by
    intro s hs
    have : M.subtype s ∈ SH := ⟨s, hs, rfl⟩
    exact hSH_le_PH this
  have hS_eq : (PH : Subgroup H).subgroupOf M = (S : Subgroup ↥M) :=
    S.is_maximal' hPH_subOf_p hS_le_PH_subOf
  -- Goal: `SH = PH`.  Suffices, then `SH = ↑PH ∈ range`.
  suffices hSH_eq : SH = (PH : Subgroup H) by exact ⟨PH, hSH_eq.symm⟩
  -- Show `SH = PH` by `le_antisymm`; `≤` is `hSH_le_PH`.
  refine le_antisymm hSH_le_PH ?_
  by_contra hPH_not_le
  -- `SH < PH`; use the normalizer condition in the nilpotent `p`-group `↥PH`.
  have hSH_lt_PH : SH < (PH : Subgroup H) := lt_of_le_of_ne hSH_le_PH (by
    intro h; exact hPH_not_le (le_of_eq h.symm))
  -- Work inside `↥PH`: `SH.subgroupOf PH < ⊤`.
  haveI : Group.IsNilpotent ↥(PH : Subgroup H) := PH.isPGroup'.isNilpotent
  have hNC : NormalizerCondition ↥(PH : Subgroup H) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥(PH : Subgroup H))
  have hSH_subOf_lt_top : SH.subgroupOf (PH : Subgroup H) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact absurd (le_antisymm hSH_le_PH htop) (by
      intro h; exact hPH_not_le (le_of_eq h.symm))
  -- `SH.subgroupOf PH < N(SH.subgroupOf PH)`.
  have hlt := hNC (SH.subgroupOf (PH : Subgroup H)) hSH_subOf_lt_top
  -- Get `t : ↥PH` with `t ∈ N(SH.subgroupOf PH)`, `t ∉ SH.subgroupOf PH`.
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  -- `↑t ∈ N_H(SH)` (transport normalizer), `↑t ∉ SH`.
  rw [← Subgroup.subgroupOf_normalizer_eq hSH_le_PH, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  set tH : H := (t : H) with htH_def
  -- `tH` normalizes `J(SH)` (since `tH ∈ N_H(SH)`), so `tH ∈ N_H(J(SH)) = M`.
  have htH_norm_JSH : tH ∈ Subgroup.normalizer (Subgroup.thompsonJ SH p) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hconj : (Subgroup.thompsonJ SH p).map (MulAut.conj tH).toMonoidHom
        = Subgroup.thompsonJ SH p :=
      Subgroup.thompsonJ_map_conj_eq_of_mem_normalizer ht_norm
    constructor
    · intro hw
      have : tH * w * tH⁻¹ ∈ (Subgroup.thompsonJ SH p).map (MulAut.conj tH).toMonoidHom :=
        ⟨w, hw, rfl⟩
      rwa [hconj] at this
    · intro hw
      have : tH * w * tH⁻¹ ∈ (Subgroup.thompsonJ SH p).map (MulAut.conj tH).toMonoidHom := by
        rw [hconj]; exact hw
      obtain ⟨z, hz, hz_eq⟩ := this
      have hzw : w = z := by
        have heq : tH * z * tH⁻¹ = tH * w * tH⁻¹ := hz_eq
        -- cancel `tH⁻¹` on the right, then `tH` on the left.
        exact (mul_left_cancel (mul_right_cancel heq)).symm
      rw [hzw]; exact hz
  have htH_in_M : tH ∈ M := hNJSH_eq_M ▸ htH_norm_JSH
  -- `tH ∈ M ∩ PH`, so `(⟨tH, _⟩ : ↥M) ∈ PH.subgroupOf M = S`, i.e. `tH ∈ SH`.
  have htH_in_PH : tH ∈ (PH : Subgroup H) := t.2
  have htM_in_S : (⟨tH, htH_in_M⟩ : ↥M) ∈ (S : Subgroup ↥M) := by
    rw [← hS_eq, Subgroup.mem_subgroupOf]; exact htH_in_PH
  have htH_in_SH : tH ∈ SH := ⟨⟨tH, htH_in_M⟩, htM_in_S, rfl⟩
  -- But `t ∉ SH.subgroupOf PH` means `↑t ∉ SH`, contradiction.
  exact ht_not htH_in_SH

/-- **§7D Step 8** (Isaacs L4045-4063) — *normal `J` and full Sylow for a
`p`-type maximal*.

Let `M` be a `p`-type maximal subgroup and `S ∈ Syl_p(M)`.  Then `J(S) ⊴ M` and
`S` is a full Sylow `p`-subgroup of `G`.

Textbook proof: verify the five hypotheses of the normal-J theorem (Thm 7.6) on
the solvable group `M` — `p`-solvable, `p ≠ 2`, Sylow-2 abelian (trivial since
Step 7), `O_{p'}(M) = O_q(M) = 1` (Step 3), and `C_M(Z(S)) = S` (the latter via
Step 6: `Z(S)` contains a `p`-central element, so a hypothetical order-`q`
subgroup `Y ⊆ C_M(Z(S))` would be normalized by `Z(S)`, contradicting Step 6).
Then `J(S) ⊴ M` by Thm 7.6, and `S` full Sylow since `T > S` would give
`T ⊆ N_G(J(S)) = M`. -/
theorem step8_normalJ_and_fullSylow
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    (S : Sylow p ↥M) :
    (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal ∧
      IsPGroup p ((S : Subgroup ↥M).map M.subtype) ∧
      ((S : Subgroup ↥M).map M.subtype) ∈
        Set.range (fun P : Sylow p H => (P : Subgroup H)) := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  -- `M ≠ ⊥`, `M ≠ ⊤`, `M` solvable.
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    have : Subsingleton ↥M := by rw [hMbot]; infer_instance
    exact hM_pType.2 (Subgroup.eq_bot_of_subsingleton _)
  have hM_ne_top : M ≠ ⊤ := hM_pType.1.ne_top
  haveI hM_sol : IsSolvable ↥M := hSubgroupsSolvable M hM_ne_top
  -- Step 7: both primes odd.
  obtain ⟨hp2, hq2⟩ := step7_p_ne_two_and_q_ne_two hpq hH_card hH_nsol hSubgroupsSolvable
  -- The five normal-J hypotheses on the group `↥M`.
  -- (1) `↥M` is `p`-solvable (it is solvable).
  haveI hM_pSep : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) ↥M := inferInstance
  -- (2) `p ≠ 2`.
  -- (3) Sylow-`2` subgroups abelian (trivial since `2 ∤ |M|`).
  have h2_not_dvd : ¬ (2 : ℕ) ∣ Nat.card ↥M :=
    two_not_dvd_card_subgroup_of_odd_primes hpq hH_card hp2 hq2 M
  have h2abelian : ∀ T : Subgroup ↥M, IsPGroup 2 T → ∀ x y : ↥T, x * y = y * x :=
    sylow2_abelian_of_two_not_dvd h2_not_dvd
  -- (4) `O_{p'}(M) = ⊥`.
  have h_oPiPrime : OddOrder.Isaacs.Ch03.oPiCore {r | r ≠ p} ↥M = ⊥ :=
    oPiCore_pPrime_eq_bot_of_isPType hpq hH_card hSubgroupsSolvable hM_pType
  -- The `normal_J` 4th hypothesis is phrased with `{q | q ≠ p}`; align the set.
  have h_oPiPrime' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} ↥M = ⊥ := h_oPiPrime
  -- (5) `C_M(Z(S)) = S`.
  have h_centralizer : Subgroup.centralizer
      (((Subgroup.center (S : Subgroup ↥M)).map (S : Subgroup ↥M).subtype) : Set ↥M)
      = (S : Subgroup ↥M) :=
    step8_centralizer_center_eq_sylow hpq hH_card hH_nsol hSubgroupsSolvable hM_pType S
  -- Conclude `J(S) ⊴ M` by the normal-J theorem.
  have hJ_normal : (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal :=
    normal_J S hp2 hM_pSep h2abelian h_oPiPrime' h_centralizer
  refine ⟨hJ_normal, ?_, ?_⟩
  · -- (2) `S.map M.subtype` is a `p`-group (image of the `p`-group `S`).
    exact (S.isPGroup'.map M.subtype)
  · -- (3) `S.map M.subtype` is a full Sylow `p`-subgroup of `H` (Step 8 second half).
    exact step8_sylow_full hpq hH_card hH_nsol hSubgroupsSolvable hM_pType S hJ_normal

/-! ### §7D Step 9 — terminal contradiction (Isaacs L4065-4093)

Step 9 is now **proven** (no longer an axiom).  We first land six reusable
helper lemmas, then `step9_core` (the WLOG-`|G|_p > |G|_q` argument), then the
dispatcher `step9_contradiction` that case-splits on which Sylow is larger. -/

/-- In a group of order `p^a q^b` (`p ≠ q` prime), a Sylow `p`-subgroup has
order `p^a`. -/
theorem sylow_p_card_eq_of_paqb
    {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (P : Sylow p H) :
    Nat.card (P : Subgroup H) = p ^ a := by
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  have hp_ne_dvd_q : ¬ p ∣ q := by
    rw [Nat.prime_dvd_prime_iff_eq hp_prime hq_prime]; exact hpq
  have hfact_p : (p ^ a * q ^ b).factorization p = a := by
    rw [Nat.factorization_mul (pow_ne_zero a hp_prime.ne_zero)
        (pow_ne_zero b hq_prime.ne_zero), Finsupp.add_apply,
        Nat.factorization_pow_self hp_prime,
        Nat.factorization_pow, Finsupp.smul_apply,
        Nat.factorization_eq_zero_of_not_dvd hp_ne_dvd_q, smul_eq_mul, mul_zero, add_zero]
  rw [P.card_eq_multiplicity, hH_card, hfact_p]

theorem sylow_inter_ne_bot_of_card_sq_gt
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (P : Sylow p H) (hcard : Nat.card H < Nat.card (P : Subgroup H) ^ 2)
    (S T : Sylow p H) :
    (S : Subgroup H) ⊓ (T : Subgroup H) ≠ ⊥ := by
  intro hbot
  have hS_card : Nat.card (S : Subgroup H) = Nat.card (P : Subgroup H) :=
    Nat.card_congr (Sylow.equiv S P).toEquiv
  have hT_card : Nat.card (T : Subgroup H) = Nat.card (P : Subgroup H) :=
    Nat.card_congr (Sylow.equiv T P).toEquiv
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
    (S : Subgroup H) (T : Subgroup H)
  rw [hbot] at hprod
  simp only [Subgroup.card_bot, mul_one] at hprod
  rw [hS_card, hT_card] at hprod
  have hST_le : Nat.card ((↑(S : Subgroup H) : Set H) * (↑(T : Subgroup H) : Set H))
      ≤ Nat.card H :=
    Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective
  rw [hprod] at hST_le
  rw [sq] at hcard
  omega


theorem exists_thompsonJ_ne
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H) :
    ∃ S T : Sylow p H,
      Subgroup.thompsonJ (S : Subgroup H) p ≠ Subgroup.thompsonJ (T : Subgroup H) p := by
  classical
  by_contra h_all_eq
  push Not at h_all_eq
  obtain ⟨hp_dvd, _⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := H)
  have hP_ne_bot : (P : Subgroup H) ≠ ⊥ := Sylow.ne_bot_of_dvd_card hp_dvd P
  set J₀ : Subgroup H := Subgroup.thompsonJ (P : Subgroup H) p with hJ₀_def
  have hJ₀_ne_bot : J₀ ≠ ⊥ := Subgroup.thompsonJ_ne_bot P.isPGroup' hP_ne_bot
  have hJ₀_pgroup : IsPGroup p J₀ :=
    P.isPGroup'.of_injective (Subgroup.inclusion (Subgroup.thompsonJ_le (P : Subgroup H) p))
      (Subgroup.inclusion_injective _)
  -- J₀ normal: conj g maps J₀ to J of the conjugate Sylow = J₀.
  have hJ₀_normal : J₀.Normal := by
    apply Subgroup.Normal.of_conjugate_fixed
    intro g
    change J₀.map (MulAut.conj g).toMonoidHom = J₀
    -- J₀.map (conj g) = J((↑P).map (conj g)) = J(↑(g • P)) = J(↑(g•P)) = J₀.
    have h1 : J₀.map (MulAut.conj g).toMonoidHom
        = Subgroup.thompsonJ ((P : Subgroup H).map (MulAut.conj g).toMonoidHom) p :=
      (Subgroup.thompsonJ_map_of_injective (MulAut.conj g).injective (P : Subgroup H) p).symm
    have h2 : (P : Subgroup H).map (MulAut.conj g).toMonoidHom
        = ((g • P : Sylow p H) : Subgroup H) :=
      Sylow.coe_subgroup_smul.symm
    rw [h1, h2, h_all_eq (g • P) P]
  have hOp_bot : OddOrder.Isaacs.Ch01.opCore p H = ⊥ :=
    opCore_eq_bot_of_simple_nonsolvable inferInstance hH_nsol
  have hJ₀_le_Op : J₀ ≤ OddOrder.Isaacs.Ch01.opCore p H :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hJ₀_pgroup
  rw [hOp_bot, le_bot_iff] at hJ₀_le_Op
  exact hJ₀_ne_bot hJ₀_le_Op

theorem exists_sylowM_of_full_sylow_le
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] {M : Subgroup H}
    (U : Sylow p H) (hUM : (U : Subgroup H) ≤ M) :
    ∃ UM : Sylow p ↥M, (UM : Subgroup ↥M).map M.subtype = (U : Subgroup H) := by
  classical
  have hUsub_p : IsPGroup p ((U : Subgroup H).subgroupOf M) := U.isPGroup'.comap_subtype
  obtain ⟨UM, hUsub_le⟩ := hUsub_p.exists_le_sylow
  refine ⟨UM, ?_⟩
  have hUM_p : IsPGroup p ((UM : Subgroup ↥M).map M.subtype) := UM.isPGroup'.map M.subtype
  have hmap_eq : ((U : Subgroup H).subgroupOf M).map M.subtype = (U : Subgroup H) := by
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, M.range_subtype]
    exact inf_eq_right.mpr hUM
  have hU_le : (U : Subgroup H) ≤ (UM : Subgroup ↥M).map M.subtype := by
    rw [← hmap_eq]; exact Subgroup.map_mono hUsub_le
  exact U.is_maximal' hUM_p hU_le

/-- §7D Step 9 bridge: for a `p`-type maximal `M` whose Sylow Thompson subgroups
are `M`-normal (Step 8), any two full Sylow `p`-subgroups of `H` lying in `M`
have the same Thompson subgroup. -/
theorem thompsonJ_eq_of_full_sylow_le_pType
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] {M : Subgroup H}
    (hStep8 : ∀ {N : Subgroup H} (_ : IsPType p N) (S : Sylow p ↥N),
      (Subgroup.thompsonJ (S : Subgroup ↥N) p).Normal)
    (hM_pType : IsPType p M)
    (U V : Sylow p H) (hUM : (U : Subgroup H) ≤ M) (hVM : (V : Subgroup H) ≤ M) :
    Subgroup.thompsonJ (U : Subgroup H) p = Subgroup.thompsonJ (V : Subgroup H) p := by
  classical
  obtain ⟨UM, hUM_eq⟩ := exists_sylowM_of_full_sylow_le U hUM
  obtain ⟨VM, hVM_eq⟩ := exists_sylowM_of_full_sylow_le V hVM
  -- J(↑U) = (J(↑UM)).map subtype.
  have hJU : Subgroup.thompsonJ (U : Subgroup H) p
      = (Subgroup.thompsonJ (UM : Subgroup ↥M) p).map M.subtype := by
    rw [← hUM_eq, Subgroup.thompsonJ_map_of_injective M.subtype_injective]
  have hJV : Subgroup.thompsonJ (V : Subgroup H) p
      = (Subgroup.thompsonJ (VM : Subgroup ↥M) p).map M.subtype := by
    rw [← hVM_eq, Subgroup.thompsonJ_map_of_injective M.subtype_injective]
  rw [hJU, hJV]
  -- Suffices: J(↑UM) = J(↑VM) in ↥M.
  suffices hJeq : Subgroup.thompsonJ (UM : Subgroup ↥M) p
      = Subgroup.thompsonJ (VM : Subgroup ↥M) p by rw [hJeq]
  -- UM, VM are M-conjugate.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) UM VM
  -- J(↑UM) ⊴ M (Step 8).
  have hJUM_normal : (Subgroup.thompsonJ (UM : Subgroup ↥M) p).Normal := hStep8 hM_pType UM
  -- J(↑VM) = J(↑(g • UM)) = J((↑UM).map (conj g)) = (J(↑UM)).map (conj g) = J(↑UM).
  have h1 : Subgroup.thompsonJ (VM : Subgroup ↥M) p
      = Subgroup.thompsonJ ((UM : Subgroup ↥M).map (MulAut.conj g).toMonoidHom) p := by
    rw [← hg]; rfl
  haveI := hJUM_normal
  rw [h1, Subgroup.thompsonJ_map_of_injective (MulAut.conj g).injective]
  -- goal: J(↑UM) = (J(↑UM)).map (conj g); use normality (map = smul = self).
  exact (Subgroup.Normal.conj_smul_eq_self g (Subgroup.thompsonJ (UM : Subgroup ↥M) p)).symm

theorem step9_core
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    (hgt : q ^ b < p ^ a)
    (hStep8 : ∀ {M : Subgroup H} (_ : IsPType p M) (S : Sylow p ↥M),
      (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal) :
    False := by
  classical
  letI : Fintype (Sylow p H) := Fintype.ofFinite _
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- For P : Sylow p H, |P| = p^a, and |P|² > |H|.
  obtain ⟨P₀⟩ := Sylow.nonempty (p := p) (G := H)
  have hP₀_card : Nat.card (P₀ : Subgroup H) = p ^ a := sylow_p_card_eq_of_paqb hpq hH_card P₀
  have hcard_sq : Nat.card H < Nat.card (P₀ : Subgroup H) ^ 2 := by
    rw [hP₀_card, hH_card, sq]
    have hpa_pos : 0 < p ^ a := pow_pos hp_prime.pos a
    calc p ^ a * q ^ b < p ^ a * p ^ a := by
          exact (Nat.mul_lt_mul_left hpa_pos).mpr hgt
      _ = p ^ a * p ^ a := rfl
  -- (1) all p-Sylow pairs meet nontrivially.
  have hinter : ∀ S T : Sylow p H, (S : Subgroup H) ⊓ (T : Subgroup H) ≠ ⊥ := fun S T =>
    sylow_inter_ne_bot_of_card_sq_gt P₀ hcard_sq S T
  -- (2) ∃ pair with distinct J.
  obtain ⟨S₀, T₀, hJ_ne⟩ := exists_thompsonJ_ne hpq hH_card hH_nsol
  -- (3) maximize |↑S ⊓ ↑T| over distinct-J pairs.
  let distinctJ : Finset (Sylow p H × Sylow p H) :=
    Finset.univ.filter (fun ST =>
      Subgroup.thompsonJ (ST.1 : Subgroup H) p ≠ Subgroup.thompsonJ (ST.2 : Subgroup H) p)
  have hne : distinctJ.Nonempty := ⟨(S₀, T₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ_ne⟩⟩
  obtain ⟨STm, hSTm_mem, hSTm_max⟩ :=
    distinctJ.exists_max_image
      (fun ST => Nat.card ((ST.1 : Subgroup H) ⊓ (ST.2 : Subgroup H) : Subgroup H)) hne
  obtain ⟨S, T⟩ := STm
  have hST_Jne : Subgroup.thompsonJ (S : Subgroup H) p ≠ Subgroup.thompsonJ (T : Subgroup H) p :=
    (Finset.mem_filter.mp hSTm_mem).2
  have hmaxJ : ∀ R₁ R₂ : Sylow p H,
      Subgroup.thompsonJ (R₁ : Subgroup H) p ≠ Subgroup.thompsonJ (R₂ : Subgroup H) p →
      Nat.card ((R₁ : Subgroup H) ⊓ (R₂ : Subgroup H) : Subgroup H) ≤
      Nat.card ((S : Subgroup H) ⊓ (T : Subgroup H) : Subgroup H) := by
    intro R₁ R₂ hR
    exact hSTm_max (R₁, R₂) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩)
  set D : Subgroup H := (S : Subgroup H) ⊓ (T : Subgroup H) with hD_def
  have hD_ne_bot : D ≠ ⊥ := hinter S T
  -- S ≠ T, ↑S ≠ ↑T.
  have hST_ne : S ≠ T := by intro h; exact hST_Jne (by rw [h])
  have hcoeST_ne : (S : Subgroup H) ≠ (T : Subgroup H) := by
    intro h; exact hST_ne (Sylow.ext h)
  -- D < ↑S (else ↑S ≤ ↑T, equal card ⇒ equal, contra).
  have hD_lt_S : D < (S : Subgroup H) := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hDS
    -- D = ↑S ⇒ ↑S ≤ ↑T ⇒ (equal card) ↑S = ↑T.
    have hS_le_T : (S : Subgroup H) ≤ (T : Subgroup H) := by
      rw [hD_def] at hDS; rw [← hDS]; exact inf_le_right
    have hcard_eq : Nat.card (S : Subgroup H) = Nat.card (T : Subgroup H) :=
      Nat.card_congr (Sylow.equiv S T).toEquiv
    exact hcoeST_ne (Subgroup.eq_of_le_of_card_ge hS_le_T (le_of_eq hcard_eq.symm))
  -- (5) N_H(D) < ⊤, maximal M ⊇ N_H(D).
  have hD_ne_top : D ≠ ⊤ := by
    intro h
    rw [h] at hD_lt_S
    exact (lt_irrefl _ (lt_of_lt_of_le hD_lt_S le_top))
  have hND_ne_top : Subgroup.normalizer (D : Set H) ≠ ⊤ := by
    intro hNtop
    have hD_normal : D.Normal := by rw [← Subgroup.normalizer_eq_top_iff]; exact hNtop
    rcases hD_normal.eq_bot_or_eq_top with hb | ht
    · exact hD_ne_bot hb
    · exact hD_ne_top ht
  obtain ⟨M, hM_max, hND_le⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom
      (Subgroup.normalizer (D : Set H))).resolve_left hND_ne_top
  -- D is a p-subgroup.
  have hD_pgroup : IsPGroup p D :=
    S.isPGroup'.of_injective (Subgroup.inclusion (le_of_lt hD_lt_S))
      (Subgroup.inclusion_injective _)
  -- (6) D < N_H(D) ⊓ ↑S.
  have hD_lt_NS : D < Subgroup.normalizer (D : Set H) ⊓ (S : Subgroup H) := by
    have := lt_normalizer_inf_sylow_of_lt S hD_lt_S
    -- normalizer of D (as subgroup) coerces to normalizer (D : Set H)
    exact this
  -- (7) M is p-type.
  -- M ≠ ⊥.
  have hD_le_M : D ≤ M := le_trans Subgroup.le_normalizer hND_le
  have hM_ne_bot : M ≠ ⊥ := by
    intro hbot; rw [hbot, le_bot_iff] at hD_le_M; exact hD_ne_bot hD_le_M
  -- p-central x centralizing D ⇒ x ∈ M.
  obtain ⟨x, hx_pcentral, hx_comm⟩ := exists_isPCentral_centralizing hp_dvd D hD_pgroup
  have hx_in_CD : x ∈ Subgroup.centralizer (D : Set H) := by
    rw [Subgroup.mem_centralizer_iff]; intro v hv; exact (hx_comm v hv).symm
  have hx_in_ND : x ∈ Subgroup.normalizer (D : Set H) := centralizer_le_normalizer D hx_in_CD
  have hx_in_M : x ∈ M := hND_le hx_in_ND
  have hM_pType : IsPType p M := by
    rcases maximal_isPType_xor_isQType hpq hH_card hSubgroupsSolvable hM_max hM_ne_bot with h | h
    · exact h.1
    · exfalso
      exact step5b_pType_no_qCentral (Ne.symm hpq) (a := b) (b := a)
        (by rw [hH_card]; ring) hH_nsol hSubgroupsSolvable h.1 hx_pcentral hx_in_M
  -- (8) Full Sylows U ⊇ M ⊓ ↑S and V ⊇ M ⊓ ↑T of H, contained in M.
  -- Generic: from a p-subgroup K ≤ M, get full Sylow W of H with ↑W ≤ M, K ≤ ↑W.
  have hfull : ∀ K : Subgroup H, K ≤ M → IsPGroup p K →
      ∃ W : Sylow p H, (W : Subgroup H) ≤ M ∧ K ≤ (W : Subgroup H) := by
    intro K hKM hK_p
    -- K.subgroupOf M is a p-group of ↥M; extend to Sylow W_M.
    have hKsub_p : IsPGroup p (K.subgroupOf M) := hK_p.comap_subtype
    obtain ⟨WM, hKsub_le⟩ := hKsub_p.exists_le_sylow
    -- (↑WM).map subtype is a full Sylow of H.
    obtain ⟨_, _, hWM_range⟩ :=
      step8_normalJ_and_fullSylow hpq hH_card hH_nsol hSubgroupsSolvable hM_pType WM
    obtain ⟨W, hW_eq⟩ := hWM_range
    simp only at hW_eq
    -- hW_eq : ↑W = (↑WM).map subtype
    refine ⟨W, ?_, ?_⟩
    · -- ↑W = (↑WM).map subtype ≤ M.
      rw [hW_eq]; exact Subgroup.map_subtype_le _
    · -- K ≤ ↑W: K = (K.subgroupOf M).map subtype ≤ (↑WM).map subtype = ↑W.
      rw [hW_eq]
      have hKmap : (K.subgroupOf M).map M.subtype = K := by
        rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, M.range_subtype]
        exact inf_eq_right.mpr hKM
      rw [← hKmap]; exact Subgroup.map_mono hKsub_le
  -- M ⊓ ↑S and M ⊓ ↑T are p-subgroups ≤ M.
  have hMS_p : IsPGroup p (M ⊓ (S : Subgroup H) : Subgroup H) :=
    S.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
      (Subgroup.inclusion_injective _)
  have hMT_p : IsPGroup p (M ⊓ (T : Subgroup H) : Subgroup H) :=
    T.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
      (Subgroup.inclusion_injective _)
  obtain ⟨U, hU_le_M, hMS_le_U⟩ := hfull (M ⊓ (S : Subgroup H)) inf_le_left hMS_p
  obtain ⟨V, hV_le_M, hMT_le_V⟩ := hfull (M ⊓ (T : Subgroup H)) inf_le_left hMT_p
  -- (9) ↑U ⊓ ↑S ⊇ N_H(D) ⊓ ↑S ⊋ D, similarly ↑V ⊓ ↑T ⊋ D.
  -- D < N_H(D) ⊓ ↑S ≤ M ⊓ ↑S ≤ ↑U; and N_H(D) ⊓ ↑S ≤ ↑U ⊓ ↑S, so D < ↑U ⊓ ↑S.
  have hNS_le_MS : Subgroup.normalizer (D : Set H) ⊓ (S : Subgroup H) ≤ M ⊓ (S : Subgroup H) :=
    inf_le_inf_right _ hND_le
  have hD_lt_US : D < (U : Subgroup H) ⊓ (S : Subgroup H) := by
    refine lt_of_lt_of_le hD_lt_NS ?_
    -- N_H(D) ⊓ ↑S ≤ ↑U ⊓ ↑S : left ≤ M⊓↑S ≤ ↑U; right ≤ ↑S.
    exact le_inf (le_trans hNS_le_MS hMS_le_U) inf_le_right
  have hD_lt_VT : D < (V : Subgroup H) ⊓ (T : Subgroup H) := by
    -- By symmetry: D = ↑S ⊓ ↑T = ↑T ⊓ ↑S; N_H(D) ⊓ ↑T ⊋ D.
    have hD_lt_T : D < (T : Subgroup H) := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro hDT
      have hT_le_S : (T : Subgroup H) ≤ (S : Subgroup H) := by
        rw [hD_def] at hDT; rw [← hDT]; exact inf_le_left
      have hcard_eq : Nat.card (T : Subgroup H) = Nat.card (S : Subgroup H) :=
        Nat.card_congr (Sylow.equiv T S).toEquiv
      exact hcoeST_ne (Subgroup.eq_of_le_of_card_ge hT_le_S (le_of_eq hcard_eq.symm)).symm
    have hD_lt_NT : D < Subgroup.normalizer (D : Set H) ⊓ (T : Subgroup H) :=
      lt_normalizer_inf_sylow_of_lt T hD_lt_T
    have hNT_le_MT : Subgroup.normalizer (D : Set H) ⊓ (T : Subgroup H) ≤ M ⊓ (T : Subgroup H) :=
      inf_le_inf_right _ hND_le
    refine lt_of_lt_of_le hD_lt_NT ?_
    exact le_inf (le_trans hNT_le_MT hMT_le_V) inf_le_right
  -- (10) J(↑S) = J(↑U) and J(↑T) = J(↑V) by maximality of |D|.
  have hJS_eq_JU :
      Subgroup.thompsonJ (S : Subgroup H) p = Subgroup.thompsonJ (U : Subgroup H) p := by
    by_contra hne
    -- (S, U) distinct-J pair with |↑S ⊓ ↑U| > |D|, contradicting hmaxJ.
    have hle := hmaxJ S U hne
    have hcard_gt : Nat.card (D : Subgroup H)
        < Nat.card ((S : Subgroup H) ⊓ (U : Subgroup H) : Subgroup H) := by
      have : ((U : Subgroup H) ⊓ (S : Subgroup H))
          = ((S : Subgroup H) ⊓ (U : Subgroup H)) := inf_comm _ _
      rw [← this]
      exact Set.Finite.card_lt_card (Set.toFinite _) (hD_lt_US : (D : Set H) ⊂ _)
    omega
  have hJT_eq_JV :
      Subgroup.thompsonJ (T : Subgroup H) p = Subgroup.thompsonJ (V : Subgroup H) p := by
    by_contra hne
    have hle := hmaxJ T V hne
    have hcard_gt : Nat.card (D : Subgroup H)
        < Nat.card ((T : Subgroup H) ⊓ (V : Subgroup H) : Subgroup H) := by
      have : ((V : Subgroup H) ⊓ (T : Subgroup H))
          = ((T : Subgroup H) ⊓ (V : Subgroup H)) := inf_comm _ _
      rw [← this]
      exact Set.Finite.card_lt_card (Set.toFinite _) (hD_lt_VT : (D : Set H) ⊂ _)
    omega
  -- (11) J(↑U) = J(↑V) (both full Sylows ≤ M, M p-type).
  have hJU_eq_JV : Subgroup.thompsonJ (U : Subgroup H) p = Subgroup.thompsonJ (V : Subgroup H) p :=
    thompsonJ_eq_of_full_sylow_le_pType hStep8 hM_pType U V hU_le_M hV_le_M
  -- (12) J(↑S) = J(↑U) = J(↑V) = J(↑T), contradiction.
  exact hST_Jne (hJS_eq_JU.trans (hJU_eq_JV.trans hJT_eq_JV.symm))

/-- **§7D Step 9** (Isaacs L4065-4093) — *the terminal contradiction*.

Now a **theorem** (was an axiom).  Dispatches on whether `|G|_p > |G|_q` or
`|G|_q > |G|_p` (the two are unequal since `p^a = q^b` is impossible for distinct
primes with `a, b ≥ 1`), running `step9_core` with the prime whose Sylow is
larger.  Step 8 (`step8_normalJ_and_fullSylow`) and the partition
(`maximal_isPType_or_isQType`) are derived internally for that prime. -/
theorem step9_contradiction
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    (_hp2 : p ≠ 2) (_hq2 : q ≠ 2) :
    False := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- a, b ≥ 1.
  have ha_pos : 0 < a := by
    by_contra h; push Not at h
    interval_cases a
    rw [pow_zero, one_mul] at hH_card
    -- p ∣ |H| = q^b ⇒ p = q.
    rw [hH_card] at hp_dvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow hp_dvd))
  have hb_pos : 0 < b := by
    by_contra h; push Not at h
    interval_cases b
    rw [pow_zero, mul_one] at hH_card
    rw [hH_card] at hq_dvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp
      (hq_prime.dvd_of_dvd_pow hq_dvd)).symm
  -- p^a ≠ q^b.
  have hpa_ne_qb : p ^ a ≠ q ^ b := by
    intro heq
    -- p ∣ p^a = q^b ⇒ p = q.
    have : p ∣ q ^ b := heq ▸ dvd_pow_self p ha_pos.ne'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow this))
  have hH_card_swap : Nat.card H = q ^ b * p ^ a := by rw [hH_card]; ring
  rcases lt_or_gt_of_ne hpa_ne_qb with hlt | hgt
  · -- p^a < q^b: run core with (q, p) swapped.
    -- need hStep8 for q-type and partition for q.
    have hStep8' : ∀ {M : Subgroup H} (_ : IsPType q M) (S : Sylow q ↥M),
        (Subgroup.thompsonJ (S : Subgroup ↥M) q).Normal := by
      intro M hM S
      exact (step8_normalJ_and_fullSylow (Ne.symm hpq) hH_card_swap hH_nsol
        hSubgroupsSolvable hM S).1
    exact step9_core (Ne.symm hpq) hH_card_swap hH_nsol hSubgroupsSolvable hlt hStep8'
  · -- p^a > q^b: run core directly.
    have hStep8' : ∀ {M : Subgroup H} (_ : IsPType p M) (S : Sylow p ↥M),
        (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal := by
      intro M hM S
      exact (step8_normalJ_and_fullSylow hpq hH_card hH_nsol hSubgroupsSolvable hM S).1
    exact step9_core hpq hH_card hH_nsol hSubgroupsSolvable hgt hStep8'

/-- **§7D — no finite simple non-solvable group of order `p^a q^b`** (Isaacs
§7D, Thm 7.8 contradiction).

Now a **theorem**, threading the per-step decomposition:
* Step 2 (`step2_*`, proven) — complementary Sylow product.
* Step 3 (`step3_not_both_opCore_ne_bot`, axiom) + partition
  (`maximal_isPType_or_isQType`, proven) — `p`-type XOR `q`-type dichotomy.
* Steps 4-6 (`step4_*`, `step6_*`, axioms) — `q`-central elements normalize no
  nontrivial `p`-subgroup.
* Step 7 (`step7_p_ne_two_and_q_ne_two`, proven from Step 6) — both primes odd.
* Step 8 (`step8_normalJ_and_fullSylow`, axiom) — `J(S) ⊴ M` for `p`-type `M`.
* Step 9 (`step9_contradiction`, axiom) — terminal contradiction. -/
theorem noNonsolvableSimplePaQb.{u}
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (H : Type u) [Group H] [Finite H]
    (hH_simple : IsSimpleGroup H)
    (hH_nsol : ¬ IsSolvable H)
    (hH_order : ∃ a b : ℕ, Nat.card H ∣ p ^ a * q ^ b)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K) :
    False := by
  classical
  haveI := hH_simple
  -- Upgrade |H| ∣ p^a q^b to an exact equality |H| = p^a' q^b'.
  obtain ⟨a, b, hH_dvd⟩ := hH_order
  obtain ⟨a', b', hH_card⟩ : ∃ a' b' : ℕ, Nat.card H = p ^ a' * q ^ b' :=
    ⟨_, _, card_eq_pow_mul_pow_of_dvd Fact.out Fact.out hpq Nat.card_pos.ne' hH_dvd⟩
  -- Step 7: p, q both odd.
  obtain ⟨hp2, hq2⟩ :=
    step7_p_ne_two_and_q_ne_two hpq hH_card hH_nsol hSubgroupsSolvable
  -- Partition: every maximal (≠ ⊥) is p-type or q-type.
  have hPartition : ∀ {M : Subgroup H}, IsCoatom M → M ≠ ⊥ →
      IsPType p M ∨ IsQType q M := by
    intro M hM_max hM_ne_bot
    exact maximal_isPType_or_isQType hpq hH_card hM_max hM_ne_bot
      (hSubgroupsSolvable M hM_max.1)
  -- Step 8 packaged.
  have hStep8 : ∀ {M : Subgroup H} (_ : IsPType p M) (S : Sylow p ↥M),
      (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal := by
    intro M hM_pType S
    exact (step8_normalJ_and_fullSylow hpq hH_card hH_nsol hSubgroupsSolvable hM_pType S).1
  -- Step 9: terminal contradiction.
  exact step9_contradiction hpq hH_card hH_nsol hSubgroupsSolvable hp2 hq2

/-- **Isaacs Thm 7.8** (Burnside `p^a q^b` solvability).

> If `|G| = p^a * q^b` for primes `p, q`, then `G` is solvable.

The textbook proof (Isaacs p.219-222) is the character-free
**Goldschmidt-Bender-Matsuyama 9-step argument**: assume `G` is a minimum
counterexample (non-solvable group of minimum order `p^a q^b`).  Steps 1-3
establish that `G` is simple and identify maximal subgroups of `p`-type or
`q`-type; Steps 4-7 develop `p`-central element machinery and apply
Matsuyama 2.13 to force `p, q` odd; Step 8 applies the **normal-J theorem
(Thm 7.6)** to get `J(S) ⊴ M` for `S ∈ Syl_p(M)`; Step 9 derives a
contradiction from `J(S) ⊴ M` together with Thompson factorization
properties of `M`.

**Implementation strategy**: the actual 9-step argument is encapsulated in
the local axiom `noNonsolvableSimplePaQb` (issue 0032).  We carry out the
strong-induction-on-`Nat.card` reduction, peel off the simplicity reduction
via `isSimpleGroup_of_minCounterexample`, then invoke the axiom. -/
theorem burnside_p_pow_q_pow.{u}
    {G : Type u} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q)
    (hG_order : ∃ a b : ℕ, Nat.card G = p ^ a * q ^ b) :
    IsSolvable G := by
  classical
  -- Strong induction on `Nat.card` via an explicit motive over arbitrary finite
  -- groups whose order divides `|G|`.
  let motive : ℕ → Prop := fun n =>
    ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H ∣ Nat.card G → Nat.card H = n → IsSolvable H
  suffices hmain : motive (Nat.card G) by
    exact hmain G dvd_rfl rfl
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih H _ _ hH_dvd hH_card
  -- Apply the minimum-counterexample contradiction.
  by_contra hH_nsol
  have hG_pos : 0 < Nat.card G := Nat.card_pos
  have hH_pos : 0 < Nat.card H := Nat.pos_of_dvd_of_pos hH_dvd hG_pos
  -- Subgroup orders divide the ambient order; use Lagrange + IH.
  -- Every proper subgroup (not necessarily normal) is solvable.
  have hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K := by
    intro K hK_top
    have hK_dvd_H : Nat.card K ∣ Nat.card H := K.card_subgroup_dvd_card
    have hK_dvd_G : Nat.card K ∣ Nat.card G := hK_dvd_H.trans hH_dvd
    have hK_le : Nat.card K ≤ Nat.card H := Nat.le_of_dvd hH_pos hK_dvd_H
    have hK_ne : Nat.card K ≠ Nat.card H := fun h_eq =>
      hK_top (Subgroup.eq_top_of_card_eq _ h_eq)
    have hK_lt : Nat.card K < n :=
      (lt_of_le_of_ne hK_le hK_ne).trans_eq hH_card
    exact ih (Nat.card K) hK_lt K hK_dvd_G rfl
  -- Restriction of the above to normal proper subgroups.
  have hN_solvable :
      ∀ N : Subgroup H, N ≠ ⊤ → N.Normal → IsSolvable N := fun N hN _ =>
    hSubgroupsSolvable N hN
  -- Quotient orders divide the ambient order; use index-bound + IH.
  have hQ_solvable :
      ∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ → IsSolvable (H ⧸ N) := by
    intro N hN_norm hN_bot
    have hQ_dvd_H : Nat.card (H ⧸ N) ∣ Nat.card H := N.card_quotient_dvd_card
    have hQ_dvd_G : Nat.card (H ⧸ N) ∣ Nat.card G := hQ_dvd_H.trans hH_dvd
    -- |H| = |H/N| * |N| with |N| ≥ 2 ⇒ |H/N| < |H|.
    have hN_card_two : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.mpr hN_bot
    have hH_eq : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hQ_pos : 0 < Nat.card (H ⧸ N) :=
      Nat.pos_of_dvd_of_pos hQ_dvd_H hH_pos
    have hQ_lt_H : Nat.card (H ⧸ N) < Nat.card H := by
      calc Nat.card (H ⧸ N)
          = Nat.card (H ⧸ N) * 1 := (Nat.mul_one _).symm
        _ < Nat.card (H ⧸ N) * Nat.card N :=
            Nat.mul_lt_mul_of_pos_left hN_card_two hQ_pos
        _ = Nat.card H := hH_eq.symm
    have hQ_lt : Nat.card (H ⧸ N) < n := hQ_lt_H.trans_eq hH_card
    exact ih (Nat.card (H ⧸ N)) hQ_lt (H ⧸ N) hQ_dvd_G rfl
  -- H is nontrivial: |H| = n.  If n = 1 then H is trivial which is solvable
  -- (contradicting hH_nsol).
  haveI hH_nontriv : Nontrivial H := by
    by_contra h_not_nontriv
    rw [not_nontrivial_iff_subsingleton] at h_not_nontriv
    exact hH_nsol inferInstance
  -- Step 1 reduction: H is simple.
  have hH_simple : IsSimpleGroup H :=
    isSimpleGroup_of_minCounterexample hH_nsol hN_solvable hQ_solvable
  -- Order divides p^a q^b: extract a',b' such that Nat.card H ∣ p^a' q^b'.
  obtain ⟨a, b, hG_card⟩ := hG_order
  have hH_dvd_paqb : ∃ a' b' : ℕ, Nat.card H ∣ p ^ a' * q ^ b' :=
    ⟨a, b, hG_card ▸ hH_dvd⟩
  -- Invoke the §7D core axiom.
  exact noNonsolvableSimplePaQb hpq H hH_simple hH_nsol hH_dvd_paqb
    hSubgroupsSolvable


end OddOrder.Isaacs.Ch07
