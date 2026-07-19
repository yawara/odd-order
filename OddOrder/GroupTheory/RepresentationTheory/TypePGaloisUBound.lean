/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SingerLineBound
import OddOrder.GroupTheory.RepresentationTheory.SemilinearImprimitiveBound
import OddOrder.GroupTheory.RepresentationTheory.LineScalarCharacter
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The `typeP_Galois` `u`-bound dichotomy: `|U| ≤ (p^q − 1)/(p − 1)`

The σ-theory foundation entry point (issue 9000, step 3) for Peterfalvi (13.2.c)
`basic_structure.u_bound`.  A faithful fixed-point-free abelian action of `U` on `Hbar ≅ 𝔽_p^q`
(`q` prime) satisfies `|U| ≤ (p^q − 1)/(p − 1)` regardless of `typeP_Galois`:

* **Galois** (`IsSimpleModule` — `U` irreducible): the Singer line bound
  `card_le_cyclotomicQuotient_of_faithful_irreducible_fpf` (`SingerLineBound`) gives it directly.
* **non-Galois** (reducible): the imprimitive block structure gives
  `|U| ≤ (p−1)^{q−1} ≤ (p^q−1)/(p−1)`
  (`card_le_cyclotomicQuotient_of_injective_imprimitive`, `SemilinearImprimitiveBound`).

This file packages the case split so a consumer (lane a's Pf (9.7) assembly / `basic_structure`)
cites one lemma.  The **non-Galois branch is exposed as a hypothesis** `hReducible` — the
imprimitive decomposition (`Hbar = ⊕ H1^w`, the ratio embedding `Ū ↪ ℤ_a^{q−1}`) is the
`𝔽_p`-module + `W₁`-permutation content, discharged by the caller via
`card_le_cyclotomicQuotient_of_injective_imprimitive`; the Galois branch is fully proven here.
-/

namespace OddOrder.RepresentationTheory

universe u

/-- **The qualitative block-scalar product embedding.**  Under the imprimitive block hypotheses,
the normalized scalar-ratio homomorphism embeds `U` into `n` copies of `(ZMod p)ˣ`.

This is the group-structural form of the block engine.  The cardinality and divisibility theorems
below forget this map; Peterfalvi (14.6) instead restricts it to a Sylow subgroup. -/
theorem exists_blockScalarRatioEmbedding_of_blocks {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    {n : ℕ} (ρ : Representation (ZMod p) U M) (B : Fin (n + 1) → Subrepresentation ρ)
    (hBcard : ∀ i, Nat.card (B i).toSubmodule = p)
    (hconst : ∀ u : U,
        (∀ i : Fin (n + 1),
          lineScalarChar (B i).toRepresentation
              (finrank_eq_one_of_card_eq_prime (hBcard i)) u
            = lineScalarChar (B 0).toRepresentation
                (finrank_eq_one_of_card_eq_prime (hBcard 0)) u)
        → u = 1) :
    ∃ ψ : U →* (Fin n → (ZMod p)ˣ), Function.Injective ψ :=
  ⟨blockScalarRatioHom (fun i => lineScalarChar (B i).toRepresentation
      (finrank_eq_one_of_card_eq_prime (hBcard i))),
    blockScalarRatioHom_injective _ hconst⟩

/-- **Peterfalvi (9.7)(a), order-`a` refinement of the block-scalar ratio embedding.**  Under the
same imprimitive block hypotheses, if every block scalar character is killed by `a`
(`hpow` — concretely `a = |U : C_U(H₁)|` is the common image order of the `q` block characters,
the `W₁`-conjugacy of the blocks making it independent of the block), then the ratio embedding
lands in the product of `n` copies of the **`a`-torsion subgroup** of `(ZMod p)ˣ` — the unique
cyclic subgroup of order `a` of the cyclic `(ZMod p)ˣ` when `a ∣ p − 1`.  This is the book's
"`Ū` is isomorphic to a subgroup of the direct product of `q − 1` cyclic groups of order `a`"
(p. 51), refining `exists_blockScalarRatioEmbedding_of_blocks` (whose codomain forgets the order
information; Peterfalvi (14.6) needs the `a`-form). -/
theorem exists_blockScalarRatioEmbedding_of_blocks_pow_eq_one {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    {n : ℕ} (ρ : Representation (ZMod p) U M) (B : Fin (n + 1) → Subrepresentation ρ)
    (hBcard : ∀ i, Nat.card (B i).toSubmodule = p)
    (hconst : ∀ u : U,
        (∀ i : Fin (n + 1),
          lineScalarChar (B i).toRepresentation
              (finrank_eq_one_of_card_eq_prime (hBcard i)) u
            = lineScalarChar (B 0).toRepresentation
                (finrank_eq_one_of_card_eq_prime (hBcard 0)) u)
        → u = 1)
    {a : ℕ}
    (hpow : ∀ (i : Fin (n + 1)) (u : U),
      (lineScalarChar (B i).toRepresentation
          (finrank_eq_one_of_card_eq_prime (hBcard i)) u) ^ a = 1) :
    ∃ ψ : U →* (Fin n → (ZMod p)ˣ),
      Function.Injective ψ ∧ ∀ (u : U) (i : Fin n), (ψ u i) ^ a = 1 := by
  refine ⟨blockScalarRatioHom (fun i => lineScalarChar (B i).toRepresentation
      (finrank_eq_one_of_card_eq_prime (hBcard i))),
    blockScalarRatioHom_injective _ hconst, ?_⟩
  intro u i
  change (lineScalarChar (B i.succ).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard i.succ)) u
      / lineScalarChar (B 0).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard 0)) u) ^ a = 1
  rw [div_pow, hpow, hpow, div_one]

/-- The scalar-character identity on an order-`p` subrepresentation, viewed in the ambient
representation.  This avoids exposing the subtype module's implementation instances to callers
that assemble the block identities into an equality on the whole representation. -/
theorem lineScalarChar_smul_coe_of_card_eq_prime {p : ℕ} [Fact p.Prime]
    {U M : Type u} [Group U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    (ρ : Representation (ZMod p) U M) (B : Subrepresentation ρ)
    (hBcard : Nat.card B.toSubmodule = p) (u : U) (x : B) :
    ρ u x.1 =
      (lineScalarChar B.toRepresentation
        (finrank_eq_one_of_card_eq_prime hBcard) u : ZMod p) • x.1 := by
  change (↑(B.toRepresentation u x) : M) = _
  simpa using congrArg Subtype.val
    (lineScalarChar_smul B.toRepresentation
      (finrank_eq_one_of_card_eq_prime hBcard) u x)

/-- **`typeP_Galois` `u`-bound dichotomy** (Peterfalvi (13.2.c)): a faithful, fixed-point-free
abelian `U`-action on `M ≅ 𝔽_p^q` has `|U| ≤ (p^q − 1)/(p − 1)`.

The Galois branch (`IsSimpleModule`) is discharged by the Singer line bound; the non-Galois branch
is supplied by `hReducible` (the imprimitive `u`-bound,
`card_le_cyclotomicQuotient_of_injective_imprimitive` applied to the caller's block decomposition).
Combining both is the `u_bound` field of `BasicStructureData`. -/
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

/-- **Block-scalar order divisibility** (Peterfalvi (9.7)(a)): under the same imprimitive block
hypotheses as `card_le_cyclotomicQuotient_of_blocks`, the order of `U` divides `(p - 1)^n`.

This retains the prime-factor information discarded by the cardinality bound.  In Peterfalvi
(13.13), `U` has odd order, so the 2-primary part of `(p - 1)^n` can subsequently be removed. -/
theorem card_dvd_pred_pow_of_blocks {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    {n : ℕ} (ρ : Representation (ZMod p) U M) (B : Fin (n + 1) → Subrepresentation ρ)
    (hBcard : ∀ i, Nat.card (B i).toSubmodule = p)
    (hconst : ∀ u : U,
        (∀ i : Fin (n + 1),
          lineScalarChar (B i).toRepresentation (finrank_eq_one_of_card_eq_prime (hBcard i)) u
            = lineScalarChar (B 0).toRepresentation
                (finrank_eq_one_of_card_eq_prime (hBcard 0)) u)
        → u = 1) :
    Nat.card U ∣ (p - 1) ^ n := by
  have hdvd : Nat.card U ∣ Nat.card (ZMod p)ˣ ^ n :=
    card_dvd_pow_of_block_scalars
      (fun i => lineScalarChar (B i).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard i)))
      hconst
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  rwa [hunits] at hdvd
/-- **Non-Galois `u`-bound from an imprimitive block decomposition** (Peterfalvi (9.7)(a),
module-level entry point): if the abelian `U`-action on `M` restricts to `q = n+1` order-`p`
subrepresentations `B i` (each an `𝔽_p`-line — the imprimitivity blocks `H1^w`) with **no
nonidentity element acting by a single scalar on every block** (`hconst`, i.e. `C_U(M) = 1` modulo
scalars), then `|U| ≤ (p^q − 1)/(p − 1)`.

Assembles the block scalar characters `φ_i = lineScalarChar (B i)` (the action of `U` on each line)
into `card_le_pow_of_block_scalars` (`|U| ≤ (p−1)^{q−1}`) and lifts through
`pow_sub_one_le_cyclotomicQuotient`.  This discharges the `hReducible` branch of
`card_le_cyclotomicQuotient_of_faithful_fpf`: the caller (the Pf (9.7)(a) assembly, lane a) supplies
only the block subrepresentations and `hconst` — the `W₁`-permuted `𝔽_p`-module content; scalar
extraction, the ratio embedding, and the arithmetic are all discharged here. -/
theorem card_le_cyclotomicQuotient_of_blocks {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    {n : ℕ} (ρ : Representation (ZMod p) U M) (B : Fin (n + 1) → Subrepresentation ρ)
    (hBcard : ∀ i, Nat.card (B i).toSubmodule = p)
    (hconst : ∀ u : U,
        (∀ i : Fin (n + 1),
          lineScalarChar (B i).toRepresentation (finrank_eq_one_of_card_eq_prime (hBcard i)) u
            = lineScalarChar (B 0).toRepresentation (finrank_eq_one_of_card_eq_prime (hBcard 0)) u)
        → u = 1) :
    Nat.card U ≤ (p ^ (n + 1) - 1) / (p - 1) := by
  have hb : Nat.card U ≤ Nat.card (ZMod p)ˣ ^ n :=
    card_le_pow_of_block_scalars
      (fun i => lineScalarChar (B i).toRepresentation (finrank_eq_one_of_card_eq_prime (hBcard i)))
      hconst
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  rw [hunits] at hb
  calc Nat.card U ≤ (p - 1) ^ n := hb
    _ ≤ (p ^ (n + 1) - 1) / (p - 1) := by
        have h := pow_sub_one_le_cyclotomicQuotient (p := p) (q := n + 1)
          (Fact.out : p.Prime).two_le (by omega)
        simpa using h

end OddOrder.RepresentationTheory
