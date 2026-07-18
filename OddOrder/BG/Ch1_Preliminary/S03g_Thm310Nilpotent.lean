/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310FixedPointSplit
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310GroupForm
import OddOrder.BG.Ch1_Preliminary.S03h_Thm38
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.GroupTheory.MinimalInvariantNormal
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import Mathlib.Algebra.Group.Action.End

/-!
# BG Theorem 3.10 for a general nilpotent `M` — the group-level Case-1 induction
*(LMS LNS 188, §3, mmd L1287-1317; issue 3011 piece 3.)*

**Statement.** Let a finite solvable group `H = KR` (a Frobenius group with kernel `K ⊴ H` and
complement `R`) act on a finite nontrivial **nilpotent** group `M` via `MulDistribMulAction H M`,
coprimely (`(|H|, |M|) = 1`), with `C_M(K) = 1` and the "prime manner" condition `C_M(⟨x⟩) = C_M(R)`
for every `x ∈ R^#`.  Then:

* **(b)** `|M| = |C_M(R)| ^ |R|`;
* **(c)** if `C_M(R)` is cyclic then the kernel's derived subgroup acts trivially: every
  `g ∈ ⁅K, K⁆` fixes every `m ∈ M`.

Here `C_M(R) = fixedSubgroup (MulDistribMulAction.toMulAut H M) R`.  Part (a) (`R` of prime order)
is `M`-independent and is provided elsewhere.

## Proof (Case 1, dévissage on `|M|`)

The proof is a strong induction on `Nat.card M`, phrased uniformly in the `MulAut`-framework action
`φ : H →* MulAut M` (`bgThm310_nilpotent_aux`).  Only **solvability** of `M` is used, so the
auxiliary is stated for solvable `M` (nilpotent `⟹` solvable); the headline `bgThm310_nilpotent`
specialises it to the nilpotent hypothesis of the book.

`exists_aInvariant_normal_isElementaryAbelian` (`OddOrder.GroupTheory.MinimalInvariantNormal`) hands
a *minimal* `H`-invariant normal subgroup `N ◁ M`, which is elementary abelian.

* **`N = ⊤` (base, `M` is `H`-chief hence elementary abelian).**  Give `M` a `CommGroup`
  structure, a `ZMod p`-module structure on `Additive M`, and the `MulDistribMulAction H M` from
  `φ` (all *freshly* via `MulDistribMulAction.compHom`), then apply the elementary-abelian base case
  `bgThm310_elemAbelian_group` (piece 2).  The bridge `MulDistribMulAction.toMulAut H M = φ`
  identifies the two fixed-point conventions.
* **`N ⊊ ⊤` (step).**  Apply the induction hypothesis to `↥N` (restricted action `hN.restrict`) and
  to `M ⧸ N` (induced action `hN.quotientMulAutHom`), restricting the hypotheses:
  `C_{↥N}(-) = C_M(-) ⊓ N` (`fixedSubgroup_restrict_eq_subgroupOf`) and, for the quotient,
  BG Prop 1.5(d) in subgroup form `C_{M/N}(-) = C_M(-)·N/N`
  (`fixedSubgroup_quotientMulAutHom_eq_map`).  Then:
  - **(b)-glue**: `|M| = |M/N|·|↥N|`, the two induction hypotheses, and the Hartley–Turull order
    split (piece 1, `card_fixedSubgroup_eq_mul_of_invariantNormal`)
    `|C_M(R)| = |C_{↥N}(R)|·|C_{M/N}(R)|`.
  - **(c)-glue**: cyclic `C_M(R)` makes `C_{↥N}(R)` (a subgroup) and `C_{M/N}(R)` (a quotient image)
    cyclic, so the induction hypotheses give `⁅K, K⁆` acting trivially on `↥N` and on `M/N`; the
    two-step chain stabiliser BG Lemma 1.9
    (`OddOrder.BG.Ch1.S01.coprime_actsTrivially_of_normal_and_quotient`) lifts this to `M`.
-/

namespace OddOrder.BG.Ch1.S03g

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03 (IsAInvariant)
open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

variable {H M : Type*} [Group H] [Group M]

/-! ### Two transfer bridges for the induction step -/

/-- **Restriction bridge**: the `B`-fixed points of the action restricted to an invariant normal
`N` are exactly `C_M(B) ⊓ N`, i.e. `(fixedSubgroup φ B).subgroupOf N`.  (Both membership predicates
are `∀ l ∈ B, φ l (x : M) = (x : M)`.) -/
private theorem fixedSubgroup_restrict_eq_subgroupOf {φ : H →* MulAut M} {N : Subgroup M}
    (hN : IsAInvariant φ N) (B : Subgroup H) :
    fixedSubgroup hN.restrict B = (fixedSubgroup φ B).subgroupOf N := by
  ext x
  simp only [mem_fixedSubgroup, Subgroup.mem_subgroupOf]
  constructor
  · intro h l hl
    have h2 := congrArg Subtype.val (h l hl)
    rwa [IsAInvariant.restrict_apply_val] at h2
  · intro h l hl
    apply Subtype.ext
    rw [IsAInvariant.restrict_apply_val]
    exact h l hl

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **BG Proposition 1.5(d), fixed-subgroup form** (`C_{M/N}(B) = C_M(B)·N / N`): for a coprime
action `φ : H → MulAut M`, an `H`-invariant normal `N ⊴ M`, and any `B ≤ H`, the `B`-fixed points of
the induced action on `M ⧸ N` are the image of `C_M(B)` under `mk' N`.  The `⊇` direction is
immediate; the `⊆` direction lifts a fixed coset via `coprime_fixedPoints_quotient` (Prop 1.5(d),
element form), applied to the acting subgroup `↥B`. -/
private theorem fixedSubgroup_quotientMulAutHom_eq_map [Finite H] [Finite M] {φ : H →* MulAut M}
    (hCop : Nat.Coprime (Nat.card H) (Nat.card M)) (hSolv : IsSolvable H ∨ IsSolvable M)
    {N : Subgroup M} [N.Normal] (hN : IsAInvariant φ N) (B : Subgroup H) :
    fixedSubgroup hN.quotientMulAutHom B = (fixedSubgroup φ B).map (QuotientGroup.mk' N) := by
  refine le_antisymm ?_ ?_
  · intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [mem_fixedSubgroup] at hq
    have hCopB : Nat.Coprime (Nat.card ↥B) (Nat.card M) :=
      hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B)
    have hSolvB : IsSolvable ↥B ∨ IsSolvable M := by
      rcases hSolv with h | h
      · exact Or.inl inferInstance
      · exact Or.inr h
    have hNB : IsAInvariant (φ.comp B.subtype) N := fun a => hN (B.subtype a)
    have hg_fix : ∀ a : ↥B, ∃ n ∈ N, (φ.comp B.subtype a) g = g * n := by
      intro a
      have hqa := hq (a : H) a.2
      rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hqa
      exact ⟨g⁻¹ * (φ (a : H)) g, by simpa using N.inv_mem hqa,
        by change (φ (a : H)) g = g * (g⁻¹ * (φ (a : H)) g); group⟩
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (A := ↥B) (φ := φ.comp B.subtype)
        hCopB hSolvB hNB hg_fix
    refine Subgroup.mem_map.mpr ⟨c, ?_, ?_⟩
    · rw [mem_fixedSubgroup]; intro l hl; exact hc_fix ⟨l, hl⟩
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hcn]
      simpa using N.inv_mem hn
  · rw [Subgroup.map_le_iff_le_comap]
    intro c hc
    rw [mem_fixedSubgroup] at hc
    rw [Subgroup.mem_comap, mem_fixedSubgroup]
    intro l hl
    rw [quotientMulAutHom_apply_mk', hc l hl]

/-! ### The Case-1 strong induction -/

/-- **BG Theorem 3.10 (b)+(c), `MulAut`-framework auxiliary** (issue 3011 piece 3).  Strong
induction on `|M|` for a finite *solvable* `M` with an automorphic `H`-action `φ`; `H = KR` is a
fixed finite solvable Frobenius group.  See the module docstring for the dévissage. -/
private theorem bgThm310_nilpotent_aux
    [Finite H] [IsSolvable H] {K R : Subgroup H} [K.Normal]
    (hIsFrob : IsFrobeniusGroup H K R) (hRne : R ≠ ⊥) (hKne : K ≠ ⊥) :
    ∀ (n : ℕ) {M : Type*} [Group M] [Finite M] [Nontrivial M] [IsSolvable M]
      (φ : H →* MulAut M),
      Nat.Coprime (Nat.card H) (Nat.card M) →
      fixedSubgroup φ K = ⊥ →
      (∀ x ∈ R, x ≠ 1 → fixedSubgroup φ (Subgroup.zpowers x) = fixedSubgroup φ R) →
      Nat.card M = n →
      Nat.card M = Nat.card ↥(fixedSubgroup φ R) ^ Nat.card ↥R ∧
        (IsCyclic ↥(fixedSubgroup φ R) → ∀ g ∈ ⁅K, K⁆, ∀ m : M, φ g m = m) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro M _ _ _ _ φ hcop hCK hcond3 hn
    -- A minimal `H`-invariant normal subgroup `N ◁ M`; it is elementary abelian.
    obtain ⟨N, p, hp, hNne, hNnorm, hNinv, hNea⟩ :=
      exists_aInvariant_normal_isElementaryAbelian (φ := φ)
    haveI : N.Normal := hNnorm
    by_cases hNtop : N = ⊤
    · -- **Base case**: `M` is `H`-chief, hence elementary abelian; apply piece 2.
      haveI : Fact p.Prime := ⟨hp⟩
      have hMea : IsElementaryAbelian p M :=
        IsElementaryAbelian.of_mulEquiv Subgroup.topEquiv (hNtop ▸ hNea)
      letI cg : CommGroup M := { (inferInstance : Group M) with mul_comm := fun a b => hMea.comm a b }
      have hnsmul : ∀ x : Additive M, (p : ℕ) • x = 0 := by
        intro x
        apply Additive.toMul.injective
        show (p • x).toMul = (0 : Additive M).toMul
        rw [toMul_nsmul, toMul_zero]
        exact hMea.pow_eq_one x.toMul
      letI : Module (ZMod p) (Additive M) := AddCommGroup.zmodModule hnsmul
      letI actInst : MulDistribMulAction H M := MulDistribMulAction.compHom M φ
      -- The `toMulAut` of the fresh action agrees with `φ`.
      have hbridge : MulDistribMulAction.toMulAut H M = φ :=
        MonoidHom.ext fun l => MulEquiv.ext fun m => rfl
      -- `p ∤ |H|` from coprimality (`p ∣ |M|`).
      have hpdvdM : p ∣ Nat.card M := by
        rcases hMea.isPGroup.card_eq_or_dvd with h1 | h2
        · have : (1 : ℕ) < Nat.card M := Finite.one_lt_card_iff_nontrivial.mpr ‹Nontrivial M›
          omega
        · exact h2
      have hpH : ¬ p ∣ Nat.card H := by
        intro hpH
        have hgcd : p ∣ Nat.gcd (Nat.card H) (Nat.card M) := Nat.dvd_gcd hpH hpdvdM
        rw [hcop] at hgcd
        exact hp.one_lt.ne' (Nat.dvd_one.mp hgcd)
      have hcopRK : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K) :=
        hIsFrob.coprime_card_kernel_complement.symm
      -- Apply the elementary-abelian base case (piece 2), then bridge back to `φ`.
      have hpiece2 := bgThm310_elemAbelian_group (p := p) (M := M) (K := K) (R := R)
        hIsFrob hRne hKne hpH hcopRK (by rw [hbridge]; exact hCK)
        (by intro x hx hx1; rw [hbridge]; exact hcond3 x hx hx1)
      refine ⟨?_, ?_⟩
      · have hb := hpiece2.1; rw [hbridge] at hb; exact hb
      · intro hcyc g hg m
        have hc := hpiece2.2; rw [hbridge] at hc
        exact hc hcyc g hg m
    · -- **Step case**: peel off the proper elementary-abelian `N` and recurse.
      haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
      haveI : Nontrivial (M ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
      have h1ltN : 1 < Nat.card ↥N := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      have h1ltQ : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      have hcardM_split : Nat.card M = Nat.card (M ⧸ N) * Nat.card ↥N :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup N
      have hcardN_lt : Nat.card ↥N < n := by
        rw [← hn, hcardM_split]; exact (lt_mul_iff_one_lt_left Nat.card_pos).mpr h1ltQ
      have hcardQ_lt : Nat.card (M ⧸ N) < n := by
        rw [← hn, hcardM_split]; exact (lt_mul_iff_one_lt_right Nat.card_pos).mpr h1ltN
      -- Restrict/descend the hypotheses.
      have hcopN : Nat.Coprime (Nat.card H) (Nat.card ↥N) :=
        hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card N)
      have hcopQ : Nat.Coprime (Nat.card H) (Nat.card (M ⧸ N)) :=
        hcop.coprime_dvd_right (Subgroup.card_quotient_dvd_card N)
      have hCKN : fixedSubgroup hNinv.restrict K = ⊥ := by
        rw [fixedSubgroup_restrict_eq_subgroupOf hNinv K, hCK, Subgroup.bot_subgroupOf]
      have hcond3N : ∀ x ∈ R, x ≠ 1 →
          fixedSubgroup hNinv.restrict (Subgroup.zpowers x) = fixedSubgroup hNinv.restrict R := by
        intro x hx hx1
        rw [fixedSubgroup_restrict_eq_subgroupOf hNinv (Subgroup.zpowers x),
          fixedSubgroup_restrict_eq_subgroupOf hNinv R, hcond3 x hx hx1]
      have hCKQ : fixedSubgroup hNinv.quotientMulAutHom K = ⊥ := by
        rw [fixedSubgroup_quotientMulAutHom_eq_map hcop (Or.inr ‹IsSolvable M›) hNinv K, hCK,
          Subgroup.map_bot]
      have hcond3Q : ∀ x ∈ R, x ≠ 1 →
          fixedSubgroup hNinv.quotientMulAutHom (Subgroup.zpowers x)
            = fixedSubgroup hNinv.quotientMulAutHom R := by
        intro x hx hx1
        rw [fixedSubgroup_quotientMulAutHom_eq_map hcop (Or.inr ‹IsSolvable M›) hNinv
            (Subgroup.zpowers x),
          fixedSubgroup_quotientMulAutHom_eq_map hcop (Or.inr ‹IsSolvable M›) hNinv R,
          hcond3 x hx hx1]
      -- The two induction hypotheses.
      have resN := IH (Nat.card ↥N) hcardN_lt hNinv.restrict hcopN hCKN hcond3N rfl
      have resQ := IH (Nat.card (M ⧸ N)) hcardQ_lt hNinv.quotientMulAutHom hcopQ hCKQ hcond3Q rfl
      -- The Hartley–Turull order split (piece 1).
      have hpiece1 := card_fixedSubgroup_eq_mul_of_invariantNormal hcop (Or.inr ‹IsSolvable M›)
        hNinv R
      have hb : Nat.card M = Nat.card ↥(fixedSubgroup φ R) ^ Nat.card ↥R := by
        rw [hcardM_split, resQ.1, resN.1, ← mul_pow, hpiece1]; ring
      refine ⟨hb, ?_⟩
      -- (c): assemble the two chain-stabiliser conclusions.
      intro hcyc g hg m
      haveI : IsCyclic ↥(fixedSubgroup φ R) := hcyc
      -- `C_{↥N}(R)` is cyclic: it embeds into the cyclic `C_M(R)`.
      have hcycN : IsCyclic ↥(fixedSubgroup hNinv.restrict R) := by
        -- `C_{↥N}(R)` maps isomorphically (via `N.subtype`) onto a subgroup of the cyclic `C_M(R)`.
        have hle : (fixedSubgroup hNinv.restrict R).map N.subtype ≤ fixedSubgroup φ R := by
          rintro _ ⟨x, hx, rfl⟩
          rw [mem_fixedSubgroup]
          intro l hl
          have h2 := congrArg Subtype.val ((mem_fixedSubgroup.mp hx) l hl)
          rwa [IsAInvariant.restrict_apply_val] at h2
        haveI : IsCyclic ↥((fixedSubgroup hNinv.restrict R).map N.subtype) :=
          Subgroup.isCyclic_of_le hle
        exact ((fixedSubgroup hNinv.restrict R).equivMapOfInjective N.subtype
          N.subtype_injective).isCyclic.mpr inferInstance
      -- `C_{M/N}(R)` is cyclic: it is the image of the cyclic `C_M(R)` under `mk' N`.
      have hmapQ : fixedSubgroup hNinv.quotientMulAutHom R
          = (fixedSubgroup φ R).map (QuotientGroup.mk' N) :=
        fixedSubgroup_quotientMulAutHom_eq_map hcop (Or.inr ‹IsSolvable M›) hNinv R
      have hcycQ : IsCyclic ↥(fixedSubgroup hNinv.quotientMulAutHom R) := by
        rw [hmapQ]
        exact isCyclic_of_surjective _
          ((QuotientGroup.mk' N).subgroupMap_surjective (fixedSubgroup φ R))
      -- `⁅K, K⁆` acts trivially on `↥N` and on `M/N`, then Lemma 1.9 lifts to `M`.
      have hkey := OddOrder.BG.Ch1.S01.coprime_actsTrivially_of_normal_and_quotient
        (φ := φ.comp (⁅K, K⁆ : Subgroup H).subtype) (N := N)
        (hcop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card ⁅K, K⁆))
        (Or.inr ‹IsSolvable M›) (fun a => hNinv (a : H))
        (fun a n hn => by
          have h2 := congrArg Subtype.val (resN.2 hcycN (a : H) a.2 ⟨n, hn⟩)
          rwa [IsAInvariant.restrict_apply_val] at h2)
        (fun a g' => by
          have h := resQ.2 hcycQ (a : H) a.2 (QuotientGroup.mk' N g')
          rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk',
            QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
          exact ⟨g'⁻¹ * (φ (a : H)) g', by simpa using N.inv_mem h,
            by change (φ (a : H)) g' = g' * (g'⁻¹ * (φ (a : H)) g'); group⟩)
      exact hkey ⟨g, hg⟩ m

/-! ### The book statement -/

/-- **BG Theorem 3.10 (b)+(c) for a general nilpotent `M`** (mmd L1287-1317; issue 3011 piece 3).

Let a finite solvable group `H` act (`MulDistribMulAction`) on a finite nontrivial **nilpotent**
group `M`, forming a Frobenius group `H = KR` with kernel `K ⊴ H` and complement `R`, coprimely
(`(|H|, |M|) = 1`), with `C_M(K) = 1` and the "prime manner" condition `C_M(⟨x⟩) = C_M(R)` for every
`x ∈ R^#`.  Then:

* **(b)** `|M| = |C_M(R)| ^ |R|`;
* **(c)** if `C_M(R)` is cyclic then every `g ∈ ⁅K, K⁆` fixes every `m ∈ M`.

Here `C_M(R) = fixedSubgroup (MulDistribMulAction.toMulAut H M) R`.  The proof (the Case-1 dévissage
`bgThm310_nilpotent_aux`) only uses that `M` is solvable; the nilpotent hypothesis is weakened to
`IsSolvable M` internally. -/
theorem bgThm310_nilpotent
    {H : Type*} [Group H] [Finite H] [IsSolvable H]
    {M : Type*} [Group M] [Finite M] [Nontrivial M] (hMnil : Group.IsNilpotent M)
    [MulDistribMulAction H M] {K R : Subgroup H} [K.Normal]
    (hIsFrob : IsFrobeniusGroup H K R) (hRne : R ≠ ⊥) (hKne : K ≠ ⊥)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card M))
    (hCK : fixedSubgroup (MulDistribMulAction.toMulAut H M) K = ⊥)
    (hcond3 : ∀ x ∈ R, x ≠ 1 →
      fixedSubgroup (MulDistribMulAction.toMulAut H M) (Subgroup.zpowers x)
        = fixedSubgroup (MulDistribMulAction.toMulAut H M) R) :
    Nat.card M = Nat.card ↥(fixedSubgroup (MulDistribMulAction.toMulAut H M) R) ^ Nat.card ↥R ∧
      (IsCyclic ↥(fixedSubgroup (MulDistribMulAction.toMulAut H M) R) →
        ∀ g ∈ ⁅K, K⁆, ∀ m : M, (g : H) • m = m) := by
  haveI := hMnil
  obtain ⟨hb, hc⟩ := bgThm310_nilpotent_aux hIsFrob hRne hKne (Nat.card M)
    (MulDistribMulAction.toMulAut H M) hcop hCK hcond3 rfl
  exact ⟨hb, fun hcyc g hg m => hc hcyc g hg m⟩

end OddOrder.BG.Ch1.S03g
