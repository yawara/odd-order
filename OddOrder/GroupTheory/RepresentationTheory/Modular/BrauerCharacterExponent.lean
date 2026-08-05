/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCharacter

/-!
# The Brauer character does not depend on the exponent

`brauerCharacter n ρ g` sums the lifted eigenvalues of `ρ g` over the `n`-th roots of unity of the
residue field.  The exponent `n` is only a bookkeeping device: any `n` with `ρ g ^ n = 1` gives the
same value.

That matters as soon as one restricts a representation to a subgroup.  Brauer characters of `G`
are taken at `|G|_{p'}` and those of `H ≤ G` at `|H|_{p'}`, and the two differ; but `|H|_{p'}`
divides `|G|_{p'}`, and this file says the values agree anyway.

Two things have to be checked:

* `rootLift m ζ = rootLift n ζ` for `ζ ^ m = 1` — the `m`-th lift is an `n`-th root of unity with
  the same residue, and the `n`-th lift is unique (`rootLift_unique`);
* the extra roots contribute nothing — an eigenvalue of `ρ g` satisfies `ζ ^ m = 1` because
  `ρ g ^ m = 1`, so eigenspaces at the other `n`-th roots vanish.

## Main results

* `OddOrder.RepresentationTheory.Modular.rootLift_eq_rootLift_of_dvd`
* `OddOrder.RepresentationTheory.Modular.eigenspace_eq_bot_of_pow_ne_one`
* `OddOrder.RepresentationTheory.Modular.brauerCharacter_eq_of_dvd`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Polynomial Module.End

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]

/-- **The lift of a root of unity does not depend on which exponent it is taken at.** -/
theorem rootLift_eq_rootLift_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : ¬ p ∣ n) (hn0 : n ≠ 0)
    (hm0 : m ≠ 0) {ζ : ResidueField 𝒪} (hζ : ζ ^ m = 1) :
    rootLift (𝒪 := 𝒪) m ζ = rootLift (𝒪 := 𝒪) n ζ := by
  have hm : ¬ p ∣ m := fun h => hn (h.trans hmn)
  obtain ⟨k, rfl⟩ := hmn
  have hpow : (rootLift (𝒪 := 𝒪) m ζ) ^ (m * k) = 1 := by
    rw [pow_mul, rootLift_pow_eq_one hm hm0 hζ, one_pow]
  have huniq := rootLift_unique (p := p) hn hn0 hpow
  rw [residue_rootLift hm hm0 hζ] at huniq
  exact huniq.symm

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ResidueField 𝒪) V]

omit [IsPModularSystem p 𝒪] in
/-- **An operator of order dividing `m` has no eigenvalue outside the `m`-th roots of unity.** -/
theorem eigenspace_eq_bot_of_pow_ne_one (ρ : Representation (ResidueField 𝒪) G V) {g : G} {m : ℕ}
    (hg : ρ g ^ m = 1) {ζ : ResidueField 𝒪} (hζ : ζ ^ m ≠ 1) :
    Module.End.eigenspace (ρ g) ζ = ⊥ := by
  refine Submodule.eq_bot_iff _ |>.mpr fun v hv => ?_
  have hvv : (ρ g) v = ζ • v := by
    have := Module.End.mem_eigenspace_iff.mp hv
    simpa using this
  have hpow : ∀ j : ℕ, ((ρ g) ^ j) v = ζ ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hstep : ((ρ g) ^ (j + 1)) v = ((ρ g) ^ j) ((ρ g) v) := by
          rw [pow_succ, Module.End.mul_apply]
        rw [hstep, hvv, map_smul, ih, smul_smul, ← pow_succ']
  have hfix : v = ζ ^ m • v := by
    have := hpow m
    rw [hg] at this
    simpa using this
  by_contra hv0
  have hsub : (ζ ^ m - 1) • v = 0 := by rw [sub_smul, one_smul, ← hfix, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact hζ (by linear_combination h)
  · exact hv0 h

/-- **The Brauer character is independent of the exponent** it is taken at, as long as `ρ g` has
order dividing it. -/
theorem brauerCharacter_eq_of_dvd [FiniteDimensional (ResidueField 𝒪) V]
    (ρ : Representation (ResidueField 𝒪) G V) {m n : ℕ} (hmn : m ∣ n) (hn : ¬ p ∣ n) (hn0 : n ≠ 0)
    (hm0 : m ≠ 0) {g : G} (hg : ρ g ^ m = 1) :
    brauerCharacter (𝒪 := 𝒪) m ρ g = brauerCharacter (𝒪 := 𝒪) n ρ g := by
  classical
  have hsub : nthRootsFinset m (1 : ResidueField 𝒪) ⊆ nthRootsFinset n 1 := by
    intro ζ hζ
    rw [mem_nthRootsFinset (Nat.pos_of_ne_zero hn0)]
    obtain ⟨k, rfl⟩ := hmn
    rw [pow_mul, (mem_nthRootsFinset (Nat.pos_of_ne_zero hm0) _).mp hζ, one_pow]
  calc brauerCharacter (𝒪 := 𝒪) m ρ g
      = ∑ ζ ∈ nthRootsFinset m (1 : ResidueField 𝒪),
          Module.finrank (ResidueField 𝒪) (Module.End.eigenspace (ρ g) ζ)
            • rootLift (𝒪 := 𝒪) n ζ := by
        refine Finset.sum_congr rfl fun ζ hζ => ?_
        rw [rootLift_eq_rootLift_of_dvd (p := p) hmn hn hn0 hm0
          ((mem_nthRootsFinset (Nat.pos_of_ne_zero hm0) _).mp hζ)]
    _ = ∑ ζ ∈ nthRootsFinset n (1 : ResidueField 𝒪),
          Module.finrank (ResidueField 𝒪) (Module.End.eigenspace (ρ g) ζ)
            • rootLift (𝒪 := 𝒪) n ζ := by
        refine Finset.sum_subset hsub fun ζ _ hζm => ?_
        rw [eigenspace_eq_bot_of_pow_ne_one ρ hg
            (fun h => hζm ((mem_nthRootsFinset (Nat.pos_of_ne_zero hm0) _).mpr h)),
          finrank_bot, zero_smul]
    _ = brauerCharacter (𝒪 := 𝒪) n ρ g := rfl

end OddOrder.RepresentationTheory.Modular
