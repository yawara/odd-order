/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S04_PGroupsSmallRank
import OddOrder.BG.Ch1_Preliminary.OperatorQuotientAction
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke
import OddOrder.GroupTheory.IsMetacyclic

/-!
# BG §4 — Theorem 4.12(a) (Huppert)

This file formalizes part **(a)** of BG Theorem 4.12 (Huppert), `references/bg/local-analysis.mmd`
L1588-1614:

> Suppose `p` is an odd prime, `R` is a metacyclic `p`-group, and `A` is a `p′`-group of
> operators on `R`. If `[R, A] = R` then `R` is abelian.

In the repository the operator group `A` acts through `φ : A →* MulAut R` with `(|A|, |R|)`
coprime, and `[R, A] = R` is `actionCommutator φ = ⊤`.

## Main result

* `OddOrder.BG.Ch1.S04b.isMulCommutative_of_metacyclic_actionCommutator_eq_top`

## Proof outline (mmd L1590-1614)

Because we assume `[R, A] = R` outright (`actionCommutator φ = ⊤`), the textbook's induction on
`|R|` (which only serves to reduce to the case `R = [R, A]`) is unnecessary; the proof is direct.

* If `R` is already abelian (`commutator R = ⊥`) we are done. Otherwise `R' = commutator R ≠ ⊥`,
  hence `R` is non-cyclic, and:
1. `R` metacyclic ⇒ `R'` cyclic (`IsMetacyclic.isCyclic_commutator`). Take a cyclic `A`-invariant
   `S ⊇ R'` maximal subject to those conditions
   (`exists_maximal_isCyclic_isAInvariant_commutator_le`). Then `S ⊴ R` (`normal_of_commutator_le`)
   and `S ≠ ⊥` (as `S ⊇ R' ≠ ⊥`).
2. `S` cyclic ⇒ `Aut S` abelian ⇒ `[R, A] ⊆ C_{R}(S)`, and `[R, A] = R` ⇒ `S ⊆ Z(R)`
   (`isCyclic_le_center_of_actionCommutator_eq_top`).
3. `R' ⊆ S` ⇒ `R/S` abelian. By Maschke (`exists_aInvariant_complement_in_omega1_quotient`), the
   submodule `Ω₁(R)·S/S` of `Ω₁(R/S)` has an `A`-invariant complement `X/S`. Lemma 4.10 makes
   `Ω₁(R)` elementary abelian of order `p²`. Since `X ∩ Ω₁(R) ⊆ S ∩ Ω₁(R) = Ω₁(S)` (order `p`),
   `|Ω₁(X)| ≤ p`, so `X` is cyclic (`isCyclic_of_card_omega1_le_prime`); maximality of `S` forces
   `X = S`, whence `Ω₁(R/S) = Ω₁(R)·S/S`, of order `|Ω₁(R)| / |Ω₁(S)| = p² / p = p`, so `R/S` is
   cyclic (`isCyclic_of_card_omega1_le_prime` again).
4. `S ⊆ Z(R)` and `R/S` cyclic ⇒ `R/Z(R)` cyclic ⇒ `R` abelian (Lemma 4.1,
   `commutative_of_cyclic_center_quotient`).

## References

* BG §4, Theorem 4.12(a). Huppert, _Endliche Gruppen I_ (1967), Satz III.13.5.
* Design notes: `notes/bg/s04_thm412_design_2026_05_30.md`.
-/

namespace OddOrder.BG.Ch1.S04b

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03 (IsAInvariant)
open OddOrder.Isaacs.Ch04
open OddOrder.BG.Ch1.OperatorQuotientAction
open OddOrder.BG.Ch1_Preliminary
open OddOrder.BG.Ch1.S04

/-- **BG Theorem 4.12(a)** (Huppert). Let `p` be an odd prime, `R` a metacyclic `p`-group, and
`φ : A →* MulAut R` a coprime operator action with `[R, A] = R` (`actionCommutator φ = ⊤`).
Then `R` is abelian.

mmd L1588-1614. Because `[R, A] = R` is assumed directly, no induction on `|R|` is needed. -/
theorem isMulCommutative_of_metacyclic_actionCommutator_eq_top
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    (hR : IsPGroup p R) (hmeta : OddOrder.GroupTheory.IsMetacyclic R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hRA : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤) :
    IsMulCommutative R := by
  classical
  -- If `R` is already abelian we are done; otherwise `commutator R ≠ ⊥`.
  by_cases hab : commutator R = ⊥
  · exact (commutator_eq_bot_iff R).mp hab
  -- `R` non-cyclic (a cyclic group is abelian, contradicting `commutator R ≠ ⊥`).
  have hRcyc : ¬ IsCyclic R := by
    intro hcyc
    letI := hcyc.commGroup
    exact hab (commutator_eq_bot R)
  -- ## Step 1 — construct the maximal cyclic `A`-invariant `S ⊇ R'`.
  have hcyc : IsCyclic ↥(commutator R) := hmeta.isCyclic_commutator
  obtain ⟨S, hS_inv, hS_cyc, hRprime_le, hS_max⟩ :=
    exists_maximal_isCyclic_isAInvariant_commutator_le φ hcyc
  haveI : IsCyclic ↥S := hS_cyc
  have hS_norm : S.Normal := OddOrder.Isaacs.Ch06.normal_of_commutator_le hRprime_le
  haveI := hS_norm
  -- `S ≠ ⊥` since it contains the nontrivial `commutator R`.
  have hSne : S ≠ ⊥ := fun h => hab (le_bot_iff.mp (h ▸ hRprime_le))
  haveI hS_nt : Nontrivial ↥S := S.nontrivial_iff_ne_bot.mpr hSne
  -- `R` itself is nontrivial (it has the nontrivial subgroup `S`).
  haveI hR_nt : Nontrivial R := by
    obtain ⟨x, y, hxy⟩ := hS_nt
    exact ⟨x, y, fun h => hxy (Subtype.ext h)⟩
  -- ## Step 2 — `S ⊆ Z(R)` (output of the cyclic-centralizer lemma, not an input).
  have hSZ : S ≤ Subgroup.center R :=
    isCyclic_le_center_of_actionCommutator_eq_top hS_norm hS_inv hRA
  -- ## Step 3 — Maschke integration ⇒ `R/S` cyclic.
  -- (3a) `R/S` is abelian (since `R' ⊆ S`).
  have hQab : ∀ x y : R ⧸ S, x * y = y * x :=
    isMulCommutative_iff.mp
      ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := S)).mpr hRprime_le)
  -- (3b) `p ∣ |R|` (nontrivial `p`-group).
  have hpR : p ∣ Nat.card R := by
    rcases hR.card_eq_or_dvd with h1 | hd
    · exact absurd h1 (by simpa using (Finite.one_lt_card (α := R)).ne')
    · exact hd
  -- (3c) `Ω₁(R)` is `A`-invariant (characteristic).
  have hWinv : IsAInvariant φ (Omega R p 1) := IsAInvariant.of_characteristic φ
  -- (3d) the image of `Ω₁(R)` under `mk' S` lands in `Ω₁(R/S)`.
  have hWΩ : (Omega R p 1).map (QuotientGroup.mk' S) ≤ Omega (R ⧸ S) p 1 := by
    rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
    rintro g (hg : g ^ (p ^ 1) = 1)
    change g ∈ Subgroup.comap (QuotientGroup.mk' S) (Omega (R ⧸ S) p 1)
    rw [Subgroup.mem_comap]
    refine Omega.mem_of_pow_eq_one ?_
    rw [← map_pow, hg, map_one]
  -- (3e) Maschke complement `X` to `Ω₁(R)·S/S` inside `Ω₁(R/S)`.
  obtain ⟨X, hSX, hXinv, _hXΩ, hXinf, hXsup⟩ :=
    exists_aInvariant_complement_in_omega1_quotient hpR hcop hS_inv hQab hWinv hWΩ
  -- (3g) `Ω₁(R)` elementary abelian of order `p²` (Lemma 4.10, non-cyclic case).
  obtain ⟨hΩR_ea, hΩR_card⟩ := isElementaryAbelian_omega1_of_isMetacyclic hR hp_odd hmeta hRcyc
  -- every element of `Ω₁(R)` is `p`-torsion.
  have hΩR_pow : ∀ g : R, g ∈ Omega R p 1 → g ^ p = 1 := by
    intro g hg
    have := hΩR_ea.pow_eq_one ⟨g, hg⟩
    simpa using congrArg (Subtype.val) this
  -- `|Ω₁(S)| = p`, and its image under `S.subtype` (a subgroup of `R`) has order `p`.
  have hΩS_card : Nat.card (Omega ↥S p 1) = p :=
    card_omega1_eq_prime_of_isCyclic (hR.to_subgroup S)
  have hΩSmap_card : Nat.card ((Omega ↥S p 1).map S.subtype) = p := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hΩS_card]
  -- `(Ω₁ ↥S).map subtype = S ⊓ Ω₁(R)` (both directions via `p`-torsion in elementary abelian).
  have hΩSmap_le : (Omega ↥S p 1).map S.subtype ≤ S ⊓ Omega R p 1 := by
    rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
    rintro ⟨g, hgS⟩ (hg : (⟨g, hgS⟩ : ↥S) ^ (p ^ 1) = 1)
    change (⟨g, hgS⟩ : ↥S) ∈ Subgroup.comap S.subtype (S ⊓ Omega R p 1)
    rw [Subgroup.mem_comap]
    have hgp : g ^ p = 1 := by
      have := congrArg (Subgroup.subtype S) hg
      rwa [map_pow, pow_one, map_one] at this
    exact ⟨hgS, Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp)⟩
  have hinter_le_map : S ⊓ Omega R p 1 ≤ (Omega ↥S p 1).map S.subtype := by
    rintro x ⟨hxS, hxΩ⟩
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    refine Omega.mem_of_pow_eq_one ?_
    rw [pow_one]
    ext
    rw [SubmonoidClass.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one]
    exact hΩR_pow x hxΩ
  have hinter_eq_map : S ⊓ Omega R p 1 = (Omega ↥S p 1).map S.subtype :=
    le_antisymm hinter_le_map hΩSmap_le
  have hinter_card : Nat.card ↥(S ⊓ Omega R p 1) = p := by
    rw [hinter_eq_map, hΩSmap_card]
  -- ### `X ⊓ Ω₁(R) ≤ S` from the trivial intersection of the `mk'`-images.
  have hXinter_le_S : X ⊓ Omega R p 1 ≤ S := by
    intro x ⟨hxX, hxΩ⟩
    -- `mk' x` lies in both `X.map mk'` and `Ω₁(R).map mk'`, hence in `⊥`.
    have hmem_X : (QuotientGroup.mk' S) x ∈ X.map (QuotientGroup.mk' S) :=
      Subgroup.mem_map_of_mem _ hxX
    have hmem_W : (QuotientGroup.mk' S) x ∈ (Omega R p 1).map (QuotientGroup.mk' S) :=
      Subgroup.mem_map_of_mem _ hxΩ
    have hbot : (QuotientGroup.mk' S) x ∈
        (X.map (QuotientGroup.mk' S) ⊓ (Omega R p 1).map (QuotientGroup.mk' S)) :=
      Subgroup.mem_inf.mpr ⟨hmem_X, hmem_W⟩
    rw [hXinf, Subgroup.mem_bot] at hbot
    -- `mk' x = 1` ⇒ `x ∈ ker (mk' S) = S`.
    rwa [← QuotientGroup.ker_mk' S, MonoidHom.mem_ker]
  -- ### `|Ω₁(X)| ≤ p`, so `X` is cyclic.
  have hΩXmap_le : (Omega ↥X p 1).map X.subtype ≤ S ⊓ Omega R p 1 := by
    rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
    rintro ⟨g, hgX⟩ (hg : (⟨g, hgX⟩ : ↥X) ^ (p ^ 1) = 1)
    change (⟨g, hgX⟩ : ↥X) ∈ Subgroup.comap X.subtype (S ⊓ Omega R p 1)
    rw [Subgroup.mem_comap]
    have hgp : g ^ p = 1 := by
      have := congrArg (Subgroup.subtype X) hg
      rwa [map_pow, pow_one, map_one] at this
    have hgΩ : g ∈ Omega R p 1 := Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp)
    exact ⟨hXinter_le_S ⟨hgX, hgΩ⟩, hgΩ⟩
  have hΩX_card : Nat.card (Omega ↥X p 1) ≤ p := by
    calc Nat.card (Omega ↥X p 1)
        = Nat.card ((Omega ↥X p 1).map X.subtype) :=
          (Subgroup.card_map_of_injective X.subtype_injective).symm
      _ ≤ Nat.card ↥(S ⊓ Omega R p 1) := Subgroup.card_le_of_le hΩXmap_le
      _ = p := hinter_card
  have hX_cyc : IsCyclic ↥X := isCyclic_of_card_omega1_le_prime (hR.to_subgroup X) hp_odd hΩX_card
  -- ### maximality of `S` forces `X = S`.
  have hXS : S = X := hS_max X hXinv hX_cyc (le_trans hRprime_le hSX) hSX
  -- (3l) `Ω₁(R/S) = Ω₁(R)·S/S`.
  have hΩRS_eq : Omega (R ⧸ S) p 1 = (Omega R p 1).map (QuotientGroup.mk' S) := by
    have := hXsup
    rw [← hXS, QuotientGroup.map_mk'_self, bot_sup_eq] at this
    exact this.symm
  -- (3m) `|Ω₁(R/S)| = p` via the first isomorphism theorem for `mk' ∘ subtype`.
  have hΩRS_card : Nat.card (Omega (R ⧸ S) p 1) = p := by
    -- the hom `g : Ω₁(R) → R/S` whose range is `Ω₁(R).map mk'` and kernel `S ⊓ Ω₁(R)`.
    set g : ↥(Omega R p 1) →* R ⧸ S :=
      (QuotientGroup.mk' S).comp (Omega R p 1).subtype with hg_def
    -- range of `g` = image of `Ω₁(R)` under `mk' S`.
    have hrange : g.range = (Omega R p 1).map (QuotientGroup.mk' S) := by
      rw [hg_def, MonoidHom.range_comp, Subgroup.range_subtype]
    -- kernel of `g` = `S.subgroupOf (Ω₁(R))`, of cardinality `|S ⊓ Ω₁(R)| = p`.
    have hker : g.ker = S.subgroupOf (Omega R p 1) := by
      ext x
      simp only [hg_def, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.mem_subgroupOf]
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' S]
    have hker_card : Nat.card g.ker = p := by
      rw [hker,
        ← Subgroup.card_map_of_injective (K := S.subgroupOf (Omega R p 1))
            (f := (Omega R p 1).subtype) (Omega R p 1).subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact hinter_card
    -- first isomorphism theorem: `|Ω₁(R)| = |range g| · |ker g|`.
    have hcard_eq : Nat.card ↥(Omega R p 1) = Nat.card g.range * Nat.card g.ker := by
      have hiso : (↥(Omega R p 1) ⧸ g.ker) ≃* g.range := QuotientGroup.quotientKerEquivRange g
      have h1 : Nat.card ↥(Omega R p 1) =
          Nat.card (↥(Omega R p 1) ⧸ g.ker) * Nat.card g.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
      rw [h1, Nat.card_congr hiso.toEquiv]
    -- solve `|range g| · p = p²` for `|range g| = p`.
    have hkey : Nat.card g.range * p = p * p := by
      have : Nat.card g.range * p = Nat.card ↥(Omega R p 1) := by
        rw [hcard_eq, hker_card]
      rw [this, hΩR_card]; ring
    have hp_pos : 0 < p := (Fact.out : p.Prime).pos
    have hrng : Nat.card g.range = p := Nat.eq_of_mul_eq_mul_right hp_pos hkey
    rw [hΩRS_eq, ← hrange]; exact hrng
  have hΩRS_le : Nat.card (Omega (R ⧸ S) p 1) ≤ p := le_of_eq hΩRS_card
  -- (3n) `R/S` is cyclic.
  have hRS_cyc : IsCyclic (R ⧸ S) :=
    isCyclic_of_card_omega1_le_prime (hR.to_quotient S) hp_odd hΩRS_le
  -- ## Step 4 — `R/Z(R)` cyclic ⇒ `R` abelian (Lemma 4.1).
  -- `R/Z(R)` is a quotient of the cyclic `R/S` (since `S ≤ Z(R)`), hence cyclic.
  haveI : IsCyclic (R ⧸ S) := hRS_cyc
  have hSZ' : S ≤ (Subgroup.center R).comap (MonoidHom.id R) := by
    rw [Subgroup.comap_id]; exact hSZ
  -- the induced surjection `R/S →* R/Z(R)`.
  have hmap_surj : Function.Surjective
      (QuotientGroup.map S (Subgroup.center R) (MonoidHom.id R) hSZ') := by
    intro y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk r, by rw [QuotientGroup.map_mk]; rfl⟩
  have hRZ_cyc : IsCyclic (R ⧸ Subgroup.center R) :=
    isCyclic_of_surjective _ hmap_surj
  exact ⟨⟨commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center R))
    (le_of_eq (QuotientGroup.ker_mk' (Subgroup.center R)))⟩⟩

set_option maxHeartbeats 1000000 in
-- `actionCommutator_restrict_self_eq_top` (the internal `[T, A] = T`) unifies a deeply nested
-- operator-action term, which is heartbeat-heavy; raise the limit for this single proof.
/-- **BG Theorem 4.12(b)** (Huppert). `references/bg/local-analysis.mmd` L1616.
With `T := [R, A] = actionCommutator φ` and `C := C_R(A) = fixedPointsOfMulAut φ`, one has
`T ∩ C = 1`.

mmd L1616: "Let `T = [R, A]`. By (a) and Proposition 1.6, `[T, A] = T`, … and
`T = [T, A] × C_T(A) = T × (T ∩ C_R(A))`. Hence `T ∩ C_R(A) = 1`."

This holds for **every** metacyclic `p`-group `R` (whether or not `R` is abelian): the argument
applies part (a) to the *subgroup* `T = [R, A]`, never to `R` itself.

* `[T, A] = T` (`actionCommutator ψT = ⊤`) is the always-true internal form of Prop 1.6(b)
  (`actionCommutator_restrict_self_eq_top`);
* `T` is metacyclic (`IsMetacyclic.subgroup`), a coprime `p`-group, so part (a)
  (`isMulCommutative_of_metacyclic_actionCommutator_eq_top`) makes `T` abelian;
* Prop 1.6(d) for the abelian `T` (`fixedPoints_inf_actionCommutator_eq_bot_of_abelian`) gives
  `C_T(A) ∩ [T, A] = ⊥`; with `[T, A] = T` this is `C_T(A) = ⊥`, and
  `C_T(A) = (C_R(A)).subgroupOf T` transports it to `T ∩ C_R(A) = ⊥` in `R`.

**BG §4** Thm 4.12(b). Huppert, _Endliche Gruppen I_ (1967), Satz III.13.5.

**註.** Part (c) of Theorem 4.12 (`[R, A]` and `C_R(A)` cyclic, `R' ⊆ [R, A]`) is *false*
without the textbook's standing assumption `1 ⊂ [R, A] ⊂ R` (mmd L1618 "By (a), `1 ⊂ T ⊂ R`"):
e.g. for `p = 3`, `R = (ℤ/3)²`, and `A = ℤ/2` acting by inversion, `[R, A] = R = E₉` is not
cyclic, so `IsCyclic [R, A]` fails even though `hp_odd, hR, hmeta, hcop, hAsolv` all hold. The
faithful (c) additionally requires `actionCommutator φ ≠ ⊥` and `actionCommutator φ ≠ ⊤`. -/
theorem actionCommutator_inf_fixedPoints_eq_bot
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    (hR : IsPGroup p R) (hmeta : OddOrder.GroupTheory.IsMetacyclic R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R)) (hAsolv : IsSolvable A) :
    OddOrder.Isaacs.Ch04.actionCommutator φ ⊓ Subgroup.fixedPointsOfMulAut φ = ⊥ := by
  classical
  -- `T := [R, A]`, with its restricted operator action `ψT`.
  set T : Subgroup R := OddOrder.Isaacs.Ch04.actionCommutator φ with hT_def
  set ψT : A →* MulAut ↥T := (IsAInvariant.actionCommutator φ).toMulAutHom with hψT_def
  -- `[T, A] = T` (Prop 1.6(b), internal form — always holds).
  have hψT_top : OddOrder.Isaacs.Ch04.actionCommutator ψT = ⊤ :=
    actionCommutator_restrict_self_eq_top hcop (Or.inl hAsolv)
  -- `T` is metacyclic (subgroup of metacyclic `R`), a coprime `p`-group.
  have hT_meta : IsMetacyclic ↥T := hmeta.subgroup
  have hT_pg : IsPGroup p ↥T := hR.to_subgroup T
  have hcopT : Nat.Coprime (Nat.card A) (Nat.card ↥T) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card T) hcop
  -- Part (a) applied to `T` ⇒ `T` abelian.
  have hTab : IsMulCommutative ↥T :=
    isMulCommutative_of_metacyclic_actionCommutator_eq_top hp_odd hT_pg hT_meta hcopT hψT_top
  letI : CommGroup ↥T := { (inferInstance : Group ↥T) with mul_comm := hTab.is_comm.comm }
  -- Prop 1.6(d) for the abelian `T`: `C_T(A) ∩ [T, A] = ⊥`; with `[T, A] = T`, `C_T(A) = ⊥`.
  have hCT_bot :
      Subgroup.fixedPointsOfMulAut ψT ⊓ OddOrder.Isaacs.Ch04.actionCommutator ψT = ⊥ :=
    OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian ψT hcopT
  rw [hψT_top, inf_top_eq] at hCT_bot
  -- `C_T(A) = (C_R(A)).subgroupOf T` (membrane transport; `set` is unfolded via `hψT_def`
  -- so the `@[simp]` lemma `toMulAutHom_apply_val` fires).
  have hCident : Subgroup.fixedPointsOfMulAut ψT
      = (Subgroup.fixedPointsOfMulAut φ).subgroupOf T := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_fixedPointsOfMulAut,
      Subgroup.mem_fixedPointsOfMulAut]
    constructor
    · intro h a
      have hv := congrArg (Subtype.val) (h a)
      simpa [hψT_def] using hv
    · intro h a
      exact Subtype.ext (by simpa [hψT_def] using h a)
  rw [hCident] at hCT_bot
  -- `(C_R(A)).subgroupOf T = ⊥` ⇒ `Disjoint C_R(A) T` ⇒ `T ∩ C_R(A) = ⊥`.
  have hdisj : Disjoint (Subgroup.fixedPointsOfMulAut φ) T :=
    Subgroup.subgroupOf_eq_bot.mp hCT_bot
  rw [disjoint_iff] at hdisj
  rw [inf_comm]; exact hdisj

end OddOrder.BG.Ch1.S04b
