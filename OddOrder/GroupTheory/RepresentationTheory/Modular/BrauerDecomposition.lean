/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Jacobson.Semiprimary
import OddOrder.GroupTheory.RepresentationTheory.Modular.IrreducibleIsBlock
import OddOrder.GroupTheory.RepresentationTheory.Modular.MinimalSubrepresentation

/-!
# Every Brauer character decomposes into irreducible ones

Induction on the dimension.  A nonzero finite-dimensional representation contains a minimal
nonzero invariant subspace `W` (`exists_minimal_invariant`), which is irreducible
(`isSimpleModule_subrepresentation_of_minimal`) and hence contributes one of the
`irreducibleBrauerCharacter π i` (`exists_irreducibleBrauerCharacter_eq`); the Brauer character
is additive along `0 → W → V → V ⧸ W → 0`
(`brauerCharacter_quotient_add_subrepresentation`) and `V ⧸ W` has smaller dimension.

The identity holds at the `p`-regular elements — which is where a Brauer character is meaningful
at all, since only there is `ρ g` of order prime to `p`.  The resulting multiplicities are the
**decomposition numbers**.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_decomposition_of_finrank_le`
* `OddOrder.RepresentationTheory.Modular.exists_decomposition`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]

omit [IsPModularSystem p 𝒪] [Finite G] in
/-- The Brauer character of the zero representation vanishes. -/
theorem brauerCharacter_eq_zero_of_subsingleton {V : Type*} [AddCommGroup V]
    [Module (ResidueField 𝒪) V] [Subsingleton V] (n : ℕ)
    (ρ : Representation (ResidueField 𝒪) G V) (g : G) :
    brauerCharacter (𝒪 := 𝒪) n ρ g = 0 := by
  refine Finset.sum_eq_zero fun ζ _ => ?_
  have : Module.finrank (ResidueField 𝒪) (Module.End.eigenspace (ρ g) ζ) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [this, zero_smul]

variable (hp : p.Prime) {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
include hp hω hπ hlin hkerJ

/-- **Every Brauer character is a non-negative integer combination of the irreducible ones**, on
the `p`-regular classes.  The multiplicities are the decomposition numbers.

The second conclusion is **block-diagonality**: a constituent that actually occurs has the same
central character as the whole representation, whenever the centre acts by a scalar at all.  It
comes for free from the induction, because a scalar action both restricts to a subrepresentation
(`subrepresentation_asAlgebraHom_eq_smul`) and descends to a quotient
(`quotient_asAlgebraHom_eq_smul`), and because `exists_irreducibleBrauerCharacter_eq` produces the
Brauer character and the central character *at the same index*. -/
theorem exists_decomposition_of_finrank_le (m : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module (ResidueField 𝒪) V]
      [FiniteDimensional (ResidueField 𝒪) V] (ρ : Representation (ResidueField 𝒪) G V),
      Module.finrank (ResidueField 𝒪) V ≤ m →
      ∃ d : ι → ℕ, (∀ g : G, IsPRegular p g →
          brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) ρ g
            = ∑ i, (d i : 𝒪) * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g) ∧
        ∀ (i : ι) {z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
          {c : ResidueField 𝒪}, d i ≠ 0 →
          ρ.asAlgebraHom (z : MonoidAlgebra (ResidueField 𝒪) G) = c • LinearMap.id →
          c = MatrixModule.centralCharacterAlg π i hπ hlin z := by
  classical
  induction m with
  | zero =>
    intro V _ _ _ ρ hm
    haveI : Subsingleton V := Module.finrank_zero_iff.mp (Nat.le_zero.mp hm)
    refine ⟨0, fun g _ => by simp [brauerCharacter_eq_zero_of_subsingleton], ?_⟩
    intro i z c hi _
    exact absurd rfl hi
  | succ m ih =>
    intro V _ _ _ ρ hm
    rcases subsingleton_or_nontrivial V with _ | _
    · refine ⟨0, fun g _ => by simp [brauerCharacter_eq_zero_of_subsingleton], ?_⟩
      intro i z c hi _
      exact absurd rfl hi
    obtain ⟨W, hWinv, hWne, hWmin⟩ := exists_minimal_invariant ρ
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
    haveI := isSimpleModule_subrepresentation_of_minimal ρ hWinv hWne hWmin
    -- the minimal piece is one of the irreducibles, with matching central character
    obtain ⟨i, hi, hic⟩ := exists_irreducibleBrauerCharacter_eq (nn := nn)
      (ρ.subrepresentation W hWinv) hπ hlin
      (hkerJ ▸ IsSemisimpleModule.jacobson_le_annihilator _ _)
    -- the quotient is smaller
    have hsum := Submodule.finrank_quotient_add_finrank W
    have hWpos : 0 < Module.finrank (ResidueField 𝒪) W := Module.finrank_pos
    obtain ⟨d, hd, hdc⟩ := ih (ρ.quotient W hWinv) (by omega)
    refine ⟨d + Pi.single i 1, fun g hg => ?_, ?_⟩
    · rw [brauerCharacter_quotient_add_subrepresentation (hn0 := pRegularExponent_pos) (ρ := ρ)
        W hWinv hω (rep_pow_pRegularExponent_eq_one ρ hp hg), hd g hg, hi g]
      have hsingle : ∑ j, (((Pi.single i 1 : ι → ℕ) j : ℕ) : 𝒪) *
          irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π j g
          = irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb]
        · intro hmem
          exact absurd (Finset.mem_univ i) hmem
      simp only [Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib, hsingle]
    intro j z c hj hz
    · rcases Nat.eq_zero_or_pos (d j) with hdj | hdj
      · -- the new constituent: its central character is read off at the same index
        have hji : j = i := by
          by_contra hne
          rw [Pi.add_apply, hdj, Pi.single_eq_of_ne hne] at hj
          exact hj rfl
        subst hji
        refine hic fun mm => ?_
        apply (ρ.subrepresentation W hWinv).asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_map_smul,
          subrepresentation_asAlgebraHom_eq_smul ρ hWinv hz, AlgHom.commutes]
        simp
      · exact hdc j hdj.ne' (LinearMap.ext fun v => quotient_asAlgebraHom_eq_smul ρ hWinv hz v)

/-- **The decomposition of a Brauer character into irreducible ones.**  The multiplicities `d i`
are the decomposition numbers of the representation. -/
theorem exists_decomposition {V : Type*} [AddCommGroup V] [Module (ResidueField 𝒪) V]
    [FiniteDimensional (ResidueField 𝒪) V] (ρ : Representation (ResidueField 𝒪) G V) :
    ∃ d : ι → ℕ, (∀ g : G, IsPRegular p g →
        brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) ρ g
          = ∑ i, (d i : 𝒪) * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π i g) ∧
      ∀ (i : ι) {z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
        {c : ResidueField 𝒪}, d i ≠ 0 →
        ρ.asAlgebraHom (z : MonoidAlgebra (ResidueField 𝒪) G) = c • LinearMap.id →
        c = MatrixModule.centralCharacterAlg π i hπ hlin z :=
  exists_decomposition_of_finrank_le hp hω hπ hlin hkerJ _ ρ le_rfl

end OddOrder.RepresentationTheory.Modular
