import OddOrder.GroupTheory.RepresentationTheory.FreeBlockPermutation
import OddOrder.BG.Ch1_Preliminary.S03e_Thm35

/-!
# BG Theorem 3.10(a): module-level core

This file builds the representation-theoretic core of BG Theorem 3.10(a) on top of the free block
permutation keystone (`FreeBlockPermutation.lean`) and the weight-space machinery of §3E
(`S03e_Thm35.lean`).

The spine here is `prime_card_of_freeBlock_cond3`: a finite subgroup `R ≤ G` acting on a
finite-dimensional `V = ⨁ᵢ Wᵢ`, permuting the blocks **freely**, with the "prime action" condition
`finrank V^⟨x⟩ = finrank V^R` for every `x ∈ R^#`, has **prime order**.  The keystone gives
`finrank V = |R|·finrank V^R` and `finrank V = p·finrank V^⟨x⟩` (`p = |⟨x⟩|`); the condition forces
`|R| = p`.  BG instantiates the blocks `Wᵢ` as the weight spaces of an abelian Frobenius kernel `K`,
where the free permutation comes from the Frobenius hypothesis.

## Main statements

* `prime_card_of_freeBlock_cond3` — `|R|` prime from a free block action + the prime-action condition.
-/

open Module LinearMap

namespace OddOrder.BG.Ch1.S03

variable {F : Type*} [Field F] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The restriction of a `↥R`-action on `ι` to a subgroup `↥S` (`S ≤ R`), via the inclusion
`↥S →* ↥R`.  Used to apply the free block keystone to `R` and to `⟨x⟩ ≤ R` with the same blocks. -/
noncomputable def mulActionSubgroupOfLe {R S : Subgroup G} (hSR : S ≤ R)
    {ι : Type*} [MulAction ↥R ι] : MulAction ↥S ι :=
  MulAction.compHom ι (Subgroup.inclusion hSR)

/-- **BG Theorem 3.10(a), block form.** Let a finite subgroup `R ≤ G` act via `ρ` on a
finite-dimensional nontrivial `V = ⨁ᵢ Wᵢ` (internal direct sum), permuting the blocks **freely**
(`ρ h` maps `Wᵢ` onto `W (h • i)`, and `h • i = i ⟹ h = 1`).  If for every `x ∈ R^#` the fixed
subspaces satisfy `finrank V^⟨x⟩ = finrank V^R` (the "prime action" condition (3)), then `|R|` is
prime.

This is the heart of Theorem 3.10(a) Case 2: the keystone `finrank V = |H|·finrank V^H` applied to
`H = R` and to `H = ⟨x⟩` for an `x` of prime order `p` yields `|R|·finrank V^R = p·finrank V^⟨x⟩`,
and the condition collapses this to `|R| = p`. -/
theorem prime_card_of_freeBlock_cond3
    [FiniteDimensional F V] [Nontrivial V] (ρ : Representation F G V)
    {R : Subgroup G} [Finite ↥R] (hRne : R ≠ ⊥)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [MulAction ↥R ι]
    {W : ι → Submodule F V} (hW : DirectSum.IsInternal W)
    (hfree : ∀ (h : ↥R) (i : ι), h • i = i → h = 1)
    (hperm : ∀ (h : ↥R) (i : ι), (W i).map (ρ (h : G)) = W (h • i))
    (hcond3 : ∀ x : G, x ∈ R → x ≠ 1 →
      finrank F (Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype))
        = finrank F (Representation.invariants (ρ.comp R.subtype))) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p := by
  classical
  -- Cauchy: pick `x ∈ R` of prime order `p`.
  obtain ⟨p, hp, hpdvd⟩ := (Nat.card ↥R).exists_prime_and_dvd
    (fun h1 => hRne (Subgroup.card_eq_one.mp h1))
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) p hpdvd
  have hxR : (x₀ : G) ∈ R := x₀.2
  have hxord : orderOf (x₀ : G) = p := by
    have h := orderOf_injective R.subtype R.subtype_injective x₀
    rw [hx₀] at h; exact h
  have hxne : (x₀ : G) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hxord; exact hp.ne_one hxord.symm
  have hPR : Subgroup.zpowers (x₀ : G) ≤ R := Subgroup.zpowers_le.mpr hxR
  have hPcard : Nat.card ↥(Subgroup.zpowers (x₀ : G)) = p := by rw [Nat.card_zpowers, hxord]
  haveI : Finite ↥(Subgroup.zpowers (x₀ : G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hPR)
  -- Keystone applied to `R`.
  have hR := ρ.finrank_eq_card_mul_finrank_invariants_of_freeBlock R hW hfree hperm
  -- Keystone applied to `⟨x⟩` (same blocks, restricted action).
  letI : MulAction ↥(Subgroup.zpowers (x₀ : G)) ι := mulActionSubgroupOfLe hPR
  have hfreeP : ∀ (h : ↥(Subgroup.zpowers (x₀ : G))) (i : ι), h • i = i → h = 1 := by
    intro h i hi
    have hi' : (Subgroup.inclusion hPR h) • i = i := hi
    exact Subgroup.inclusion_injective hPR
      ((hfree (Subgroup.inclusion hPR h) i hi').trans (map_one (Subgroup.inclusion hPR)).symm)
  have hpermP : ∀ (h : ↥(Subgroup.zpowers (x₀ : G))) (i : ι),
      (W i).map (ρ (h : G)) = W (h • i) := by
    intro h i
    have h1 : ((h : G)) = ((Subgroup.inclusion hPR h : ↥R) : G) := by
      rw [Subgroup.coe_inclusion]
    rw [h1]
    exact hperm (Subgroup.inclusion hPR h) i
  have hP := ρ.finrank_eq_card_mul_finrank_invariants_of_freeBlock
    (Subgroup.zpowers (x₀ : G)) hW hfreeP hpermP
  rw [hPcard] at hP
  -- `finrank V^⟨x⟩ = finrank V^R` (the prime-action condition (3)).
  have hcond := hcond3 (x₀ : G) hxR hxne
  rw [hcond] at hP
  -- `finrank V ≥ 1`, hence `finrank V^R ≥ 1`.
  have hdRpos : 0 < finrank F (Representation.invariants (ρ.comp R.subtype)) := by
    rcases Nat.eq_zero_or_pos (finrank F (Representation.invariants (ρ.comp R.subtype)))
      with h0 | h
    · rw [h0, Nat.mul_zero] at hR
      exact absurd hR Module.finrank_pos.ne'
    · exact h
  refine ⟨p, hp, ?_⟩
  -- `|R| · dR = finrank V = p · dR`, cancel `dR`.
  exact Nat.eq_of_mul_eq_mul_right hdRpos (hR.symm.trans hP)

end OddOrder.BG.Ch1.S03
