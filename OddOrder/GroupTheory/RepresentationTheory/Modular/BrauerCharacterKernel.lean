/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.RootsOfUnitySum
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCharacter

/-!
# A Brauer character attains its degree only on its kernel

**Navarro (6.11)**: for `φ ∈ IBr(G)` and a `p`-regular `g`, one has `g ∈ ker(φ)` if and only if
`φ(g) = φ(1)`.

The Brauer character at a `p`-regular `g` is the sum of `dim V` roots of unity — one for each
eigenvalue of `ρ g`, counted with multiplicity (`sum_finrank_eigenspace_of_pow`).  If that sum
equals `dim V`, then every one of them is `1` by `eq_one_of_pow_eq_one_of_sum_eq_card'`, so every
eigenvalue of `ρ g` is `1` and the eigenspace decomposition collapses onto the eigenvalue `1`.

Navarro's proof is the equality case of the triangle inequality in `ℂ`; over the abstract
coefficient ring of a `p`-modular system that argument is not available, and
`OddOrder.Algebra.eq_one_of_pow_eq_one_of_sum_eq_card'` is what replaces it.  Irreducibility of
the representation is not used — the statement holds for any finite-dimensional one.

## Main results

* `OddOrder.RepresentationTheory.Modular.eq_one_of_brauerCharacter_eq_finrank`
* `OddOrder.RepresentationTheory.Modular.rep_eq_one_iff_brauerCharacter_eq`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Polynomial Module.End OddOrder.GroupTheory

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [HenselianLocalRing 𝒪]
  [IsPModularSystem p 𝒪]
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ResidueField 𝒪) V]
  [FiniteDimensional (ResidueField 𝒪) V]
variable (ρ : Representation (ResidueField 𝒪) G V)

/-- **Navarro (6.11), the substantial direction.**  If the Brauer character of a `p`-regular
element equals the degree, the element acts as the identity. -/
theorem eq_one_of_brauerCharacter_eq_finrank (hp : p.Prime)
    {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {g : G} (hg : IsPRegular p g)
    (h : brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) ρ g
      = (Module.finrank (ResidueField 𝒪) V : 𝒪)) :
    ρ g = 1 := by
  classical
  have hnd : ¬ p ∣ pRegularExponent p G := not_dvd_pRegularExponent hp
  have hn0 : 0 < pRegularExponent p G := pRegularExponent_pos
  set n := pRegularExponent p G with hn
  set s := nthRootsFinset n (1 : ResidueField 𝒪) with hs
  set d : ResidueField 𝒪 → ℕ := fun ζ => Module.finrank (ResidueField 𝒪) (eigenspace (ρ g) ζ)
    with hd
  have hA : (ρ g) ^ n = 1 := rep_pow_pRegularExponent_eq_one ρ hp hg
  have hdim : ∑ ζ ∈ s, d ζ = Module.finrank (ResidueField 𝒪) V :=
    sum_finrank_eigenspace_of_pow hn0 hω hA
  have hroot : ∀ ζ : ↥s, (ζ : ResidueField 𝒪) ^ n = 1 := fun ζ =>
    (mem_nthRootsFinset hn0 _).mp ζ.2
  -- index the eigenvalues with multiplicity
  have hcard : Fintype.card ((ζ : ↥s) × Fin (d (ζ : ResidueField 𝒪)))
      = Module.finrank (ResidueField 𝒪) V := by
    rw [Fintype.card_sigma, ← hdim]
    simpa using Finset.sum_attach s d
  have hsum : ∑ x : (ζ : ↥s) × Fin (d (ζ : ResidueField 𝒪)),
      rootLift n ((x.1 : ResidueField 𝒪))
      = (Fintype.card ((ζ : ↥s) × Fin (d (ζ : ResidueField 𝒪))) : 𝒪) := by
    rw [hcard, ← h, brauerCharacter, ← Finset.sum_coe_sort s, ← Finset.univ_sigma_univ,
      Finset.sum_sigma]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    rfl
  have hpow : ∀ x : (ζ : ↥s) × Fin (d (ζ : ResidueField 𝒪)),
      rootLift n ((x.1 : ResidueField 𝒪)) ^ n = 1 := fun x =>
    rootLift_pow_eq_one hnd hn0.ne' (hroot x.1)
  have hall := fun x => OddOrder.Algebra.eq_one_of_pow_eq_one_of_sum_eq_card'
    (R := 𝒪) hn0.ne' hpow hsum x
  -- every eigenvalue with a nonzero eigenspace is `1`
  have hbot : ∀ ζ ∈ s, ζ ≠ 1 → eigenspace (ρ g) ζ = ⊥ := by
    intro ζ hζs hζ
    by_contra hne
    have hpos : 0 < d ζ := Module.finrank_pos_iff.mpr
      (Submodule.nontrivial_iff_ne_bot.mpr hne)
    have hlift : rootLift n ζ = 1 := hall ⟨⟨ζ, hζs⟩, ⟨0, hpos⟩⟩
    have hres : residue 𝒪 (rootLift n ζ) = ζ :=
      residue_rootLift hnd hn0.ne' ((mem_nthRootsFinset hn0 _).mp hζs)
    exact hζ (by rw [← hres, hlift, map_one])
  -- so the eigenspace decomposition collapses onto the eigenvalue `1`
  have htop : eigenspace (ρ g) (1 : ResidueField 𝒪) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← iSup_eigenspace_eq_top_of_pow hn0 hω hA]
    refine iSup₂_le fun ζ hζ => ?_
    rcases eq_or_ne ζ 1 with rfl | hζ1
    · exact le_rfl
    · rw [hbot ζ hζ hζ1]; exact bot_le
  ext v
  have hv : v ∈ eigenspace (ρ g) (1 : ResidueField 𝒪) := htop ▸ Submodule.mem_top
  rw [mem_eigenspace_iff, one_smul] at hv
  simpa using hv

/-- **Navarro (6.11).**  For a `p`-regular `g`, the Brauer character attains its value at `1`
exactly on the kernel. -/
theorem rep_eq_one_iff_brauerCharacter_eq (hp : p.Prime)
    {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {g : G} (hg : IsPRegular p g) :
    ρ g = 1 ↔ brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) ρ g
      = brauerCharacter (𝒪 := 𝒪) (pRegularExponent p G) ρ 1 := by
  constructor
  · intro hρ
    rw [brauerCharacter, brauerCharacter, hρ, map_one]
  · intro h
    exact eq_one_of_brauerCharacter_eq_finrank ρ hp hω hg
      (by rw [h, brauerCharacter_pRegularExponent_one ρ hp])

end OddOrder.RepresentationTheory.Modular
