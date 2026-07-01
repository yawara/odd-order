/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SingerLineBound
import OddOrder.GroupTheory.RepresentationTheory.SemilinearImprimitiveBound

/-!
# The `typeP_Galois` `u`-bound dichotomy: `|U| ≤ (p^q − 1)/(p − 1)`

The σ-theory foundation entry point (issue 9000, step 3) for Peterfalvi (13.2.c)
`basic_structure.u_bound`.  A faithful fixed-point-free abelian action of `U` on `Hbar ≅ 𝔽_p^q`
(`q` prime) satisfies `|U| ≤ (p^q − 1)/(p − 1)` regardless of `typeP_Galois`:

* **Galois** (`IsSimpleModule` — `U` irreducible): the Singer line bound
  `card_le_cyclotomicQuotient_of_faithful_irreducible_fpf` (`SingerLineBound`) gives it directly.
* **non-Galois** (reducible): the imprimitive block structure gives `|U| ≤ (p−1)^{q−1} ≤ (p^q−1)/(p−1)`
  (`card_le_cyclotomicQuotient_of_injective_imprimitive`, `SemilinearImprimitiveBound`).

This file packages the case split so a consumer (lane a's Pf (9.7) assembly / `basic_structure`) cites
one lemma.  The **non-Galois branch is exposed as a hypothesis** `hReducible` — the imprimitive
decomposition (`Hbar = ⊕ H1^w`, the ratio embedding `Ū ↪ ℤ_a^{q−1}`) is the `𝔽_p`-module +
`W₁`-permutation content, discharged by the caller via
`card_le_cyclotomicQuotient_of_injective_imprimitive`; the Galois branch is fully proven here.
-/

namespace OddOrder.RepresentationTheory

universe u

/-- **`typeP_Galois` `u`-bound dichotomy** (Peterfalvi (13.2.c)): a faithful, fixed-point-free
abelian `U`-action on `M ≅ 𝔽_p^q` has `|U| ≤ (p^q − 1)/(p − 1)`.

The Galois branch (`IsSimpleModule`) is discharged by the Singer line bound; the non-Galois branch is
supplied by `hReducible` (the imprimitive `u`-bound, `card_le_cyclotomicQuotient_of_injective_imprimitive`
applied to the caller's block decomposition).  Combining both is the `u_bound` field of
`BasicStructureData`. -/
theorem card_le_cyclotomicQuotient_of_faithful_fpf
    {p q : ℕ} [Fact p.Prime] {U M : Type u}
    [CommGroup U] [Finite U] [AddCommGroup M] [Finite M]
    [Module (MonoidAlgebra (ZMod p) U) M]
    (hq : 1 ≤ q) (hcardM : Nat.card M = p ^ q)
    (hfaith : ∀ c : U, (∀ x : M, MonoidAlgebra.of (ZMod p) U c • x = x) → c = 1)
    (σ : M ≃+ M)
    (hfpf : ∀ c : U, (∀ x : M, σ (MonoidAlgebra.of (ZMod p) U c • x)
                              = MonoidAlgebra.of (ZMod p) U c • σ x) → c = 1)
    (hReducible : ¬ IsSimpleModule (MonoidAlgebra (ZMod p) U) M →
        Nat.card U ≤ (p ^ q - 1) / (p - 1)) :
    Nat.card U ≤ (p ^ q - 1) / (p - 1) := by
  by_cases hsimple : IsSimpleModule (MonoidAlgebra (ZMod p) U) M
  · haveI := hsimple
    exact card_le_cyclotomicQuotient_of_faithful_irreducible_fpf hq hcardM hfaith σ hfpf
  · exact hReducible hsimple

end OddOrder.RepresentationTheory
