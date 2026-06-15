import OddOrder.BG.Ch1_Preliminary.S03g_Thm310Core
import OddOrder.BG.Ch1_Preliminary.S03e_WeightSpan

/-!
# BG Theorem 3.10(a): module core terminal (abelian kernel)

Assembles the proven pieces into the **abelian-kernel** case of BG Theorem 3.10(a):

* free block dimension keystone (`FreeBlockPermutation.finrank_eq_card_mul_finrank_invariants_of_freeBlock`),
* the `|R|`-prime assembly (`prime_card_of_freeBlock_cond3`),
* the weight-space spanning decomposition (`S03e.iSup_weightSpace_eq_top` + `iSupIndep_weightSpace`),
* Frobenius freeness on weight characters (`weightChar_eq_one_of_conjChar_fixed`).

The blocks are the `K`-weight spaces (over an algebraically closed field, abelian `K`, `char ∤ |K|`);
the complement `R` permutes them, freely because a nonidentity complement element acts
fixed-point-freely on `K` (Frobenius) and hence fixes only the trivial character — whose weight space
is `C_V(K) = 0`.  The prime-action condition then forces `|R|` prime via the keystone.

## Main statement

* `prime_card_of_abelian_frobenius_weight`
-/

open Module
open OddOrder.BG.Ch1.S03e OddOrder.RepresentationTheory

namespace OddOrder.BG.Ch1.S03

variable {F : Type*} [Field F] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- **BG Theorem 3.10(a), abelian-kernel module case.**  Let `K ⊴ G` be abelian with `char ∤ |K|`,
acting via `ρ` on a nonzero finite-dimensional space `V` over an algebraically closed field, with
`C_V(K) = 0`.  Let `R ≤ G` (`R ≠ 1`) be such that every nonidentity element of `R` acts
fixed-point-freely by conjugation on `K` (the Frobenius condition), and the prime-action condition
`finrank V^⟨x⟩ = finrank V^R` holds for every `x ∈ R^#`.  Then `|R|` is prime.

The `K`-weight spaces decompose `V`; `R` permutes them freely (Frobenius ⟹ a nonidentity element
fixes only the trivial character, whose weight space is `C_V(K) = 0`), so the free block dimension
formula and the prime-action condition give `|R|` prime. -/
theorem prime_card_of_abelian_frobenius_weight [Finite G] [IsAlgClosed F]
    (ρ : Representation F G V) [FiniteDimensional F V] [Nontrivial V]
    {K R : Subgroup G} [K.Normal] (hRne : R ≠ ⊥)
    (hKab : ∀ a b : ↥K, (a : G) * (b : G) = (b : G) * (a : G))
    (hKcard : (Nat.card ↥K : F) ≠ 0)
    (hCVK : Representation.invariants (ρ.comp K.subtype) = ⊥)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : G, x ∈ R → x ≠ 1 →
      finrank F (Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype))
        = finrank F (Representation.invariants (ρ.comp R.subtype))) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p := by
  classical
  haveI : Finite ↥R := Subtype.finite
  -- The trivial character's weight space is `C_V(K) = 0`.
  have hTrivWS : weightSpace ρ K (fun _ => (1 : F)) = ⊥ := by
    have hset : weightSpace ρ K (fun _ => (1 : F))
        = Representation.invariants (ρ.comp K.subtype) := by
      ext v
      rw [mem_weightSpace, Representation.mem_invariants]
      constructor
      · intro h k; have := h k; rwa [one_smul] at this
      · intro h k; rw [one_smul]; exact h k
    rw [hset, hCVK]
  -- The block index set: characters with nonzero weight space.
  set ι : Type _ := {χ : ↥K → F // weightSpace ρ K χ ≠ ⊥} with hι
  -- (1) Instances on `ι`.
  haveI hindep : iSupIndep (weightSpace ρ K) := iSupIndep_weightSpace ρ hKab
  haveI : Fintype ι := hindep.fintypeNeBotOfFiniteDimensional
  -- (2) The `↥R`-action on `ι` via conjugation of characters.
  have hpres : ∀ (r : ↥R) (χ : ↥K → F), weightSpace ρ K χ ≠ ⊥ →
      weightSpace ρ K (conjChar K (r : G) χ) ≠ ⊥ := by
    intro r χ hχ
    rw [← map_weightSpace ρ (r : G) χ]
    intro hbot
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    have hmem : ρ (r : G) v ∈ (weightSpace ρ K χ).map (ρ (r : G)) := Submodule.mem_map_of_mem hv
    rw [hbot, Submodule.mem_bot] at hmem
    exact hv0 ((ρ.apply_bijective (r : G)).injective (hmem.trans (map_zero _).symm))
  letI : MulAction ↥R ι :=
    { smul := fun r i => ⟨conjChar K (r : G) i.1, hpres r i.1 i.2⟩
      one_smul := fun i => by
        apply Subtype.ext
        show conjChar K ((1 : ↥R) : G) i.1 = i.1
        rw [Subgroup.coe_one, conjChar_one]
      mul_smul := fun r s i => by
        apply Subtype.ext
        show conjChar K ((r * s : ↥R) : G) i.1 = conjChar K (r : G) (conjChar K (s : G) i.1)
        rw [Subgroup.coe_mul, conjChar_mul] }
  have hsmul : ∀ (r : ↥R) (i : ι), (r • i).val = conjChar K (r : G) i.val := fun _ _ => rfl
  -- (3) The blocks.
  set W : ι → Submodule F V := fun i => weightSpace ρ K i.val with hW_def
  -- (4) The blocks form an internal direct sum.
  have hW : DirectSum.IsInternal W := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact hindep.comp Subtype.val_injective
    · have heq : (⨆ i : ι, weightSpace ρ K i.val) = (⨆ χ : ↥K → F, weightSpace ρ K χ) := by
        apply le_antisymm
        · exact iSup_le fun i => le_iSup (weightSpace ρ K) i.val
        · refine iSup_le fun χ => ?_
          by_cases hχ : weightSpace ρ K χ = ⊥
          · rw [hχ]; exact bot_le
          · exact le_iSup (fun i : ι => weightSpace ρ K i.val) (⟨χ, hχ⟩ : ι)
      show (⨆ i : ι, weightSpace ρ K i.val) = ⊤
      rw [heq]
      exact iSup_weightSpace_eq_top ρ K hKab hKcard
  -- (5) `R` permutes the blocks.
  have hperm : ∀ (h : ↥R) (i : ι), (W i).map (ρ (h : G)) = W (h • i) := by
    intro h i
    show (weightSpace ρ K i.val).map (ρ (h : G)) = weightSpace ρ K (h • i).val
    rw [hsmul h i]
    exact map_weightSpace ρ (h : G) i.val
  -- (6) The permutation is free (Frobenius ⟹ a nonidentity element fixes only the trivial char).
  have hfree : ∀ (h : ↥R) (i : ι), h • i = i → h = 1 := by
    intro h i hfix
    by_contra hne
    have hhne : (h : G) ≠ 1 := fun hc => hne (Subtype.ext hc)
    -- The fixed equation on characters.
    have hcharfix : conjChar K (h : G) i.val = i.val := by
      have := congrArg Subtype.val hfix
      rwa [hsmul h i] at this
    -- Fixed-point-freeness of conjugation by `(h:G)⁻¹` on `K`.
    have hFPF : MonoidHom.FixedPointFree (conjNormalMulAut K (h : G)⁻¹) := by
      intro k hk
      by_contra hk1
      have hkcoe : (h : G)⁻¹ * (k : G) * ((h : G)⁻¹)⁻¹ = (k : G) := by
        have := congrArg Subtype.val hk
        rwa [conjNormalMulAut_apply_coe] at this
      have hhinvne : (h : G)⁻¹ ≠ 1 := fun hc => hhne (inv_eq_one.mp hc)
      exact hFrob (h : G)⁻¹ (R.inv_mem h.2) hhinvne (k : G) k.2
        (fun hc => hk1 (Subtype.ext hc)) hkcoe
    -- Hence `i.val` is the trivial character, whose weight space is `⊥` — contradiction.
    have htriv : i.val = fun _ => (1 : F) :=
      weightChar_eq_one_of_conjChar_fixed ρ hFPF i.2 hcharfix
    exact i.2 (by rw [htriv]; exact hTrivWS)
  -- (7) Apply the free block keystone.
  exact prime_card_of_freeBlock_cond3 ρ hRne hW hfree hperm hcond3

end OddOrder.BG.Ch1.S03
