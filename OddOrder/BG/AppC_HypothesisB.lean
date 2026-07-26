/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_NormSet

/-!
# BG Appendix C: the hypotheses (A) and (B) of Theorem C

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, §1 (p. 145).

Theorem C reads: *let `p` and `q` be two primes satisfying condition*

> **(A)** `((p^q - 1)/(p - 1), p - 1) = 1`.

*Let `P` be the additive group of `𝔽_{p^q}` and `U` the subgroup of `𝔽_{p^q}ˣ` consisting of the
elements of norm one over `𝔽_p`.  The subgroup `U` acts on `P` by multiplication and we can form
the semidirect product `H = PU`.  Let `P₀` be the image in `P` of the additive group of `𝔽_p`.
Furthermore, suppose that there is a group `G` such that hypothesis (B) below holds.*

> **(B)** *There is a monomorphism `σ : H → G`, a finite abelian `p'`-subgroup `Q` of `G`, and an
> element `y ∈ Q` such that `σ(P₀)` normalizes `Q` and `σ(P₀)^y` normalizes `U`.*

*Then `p ≤ q`.*

This file carries the two hypotheses in the book's `p, q, G`-abstract form.  It sits **upstream**
of both the Peterfalvi Section 16 development (which supplies a concrete instance of (B) along the
Feit–Thompson spine) and of `OddOrder.BG.AppC_FinalContradiction` (which assembles Theorem C), so
that the Lemma C.1--C.3 machinery can be stated against these hypotheses rather than against the
Section 16 configuration.

## Main definitions

* `conditionA p q` — condition (A).
* `primeLine p q` — the prime-field line `P₀ ≤ P ≤ H`.
* `HypothesisBAbstract p q G` — hypothesis (B).

## Implementation notes

`H = PU` is `NormSet.normOneFrobeniusGroup p q`, `P` is `NormSet.normOneFrobeniusKernel p q` and
`U` is `NormSet.normOneFrobeniusComplement p q`.  Following the book's Remark (VI) ("we will
identify `H` with its image in `G`"), the two normalizer clauses of (B) are stated for the
*images* `σ(P₀)` and `σ(U)`.
-/

namespace OddOrder.BG.AppC

open scoped Pointwise

/-- **BG Appendix C, Condition (A)**: the cyclotomic factor attached to
`F_{p^q}` is coprime to `p - 1`.

By Remark (I) this is equivalent to `q ∤ p - 1` (`NormSet.conditionA_iff_not_dvd`). -/
def conditionA (p q : ℕ) : Prop :=
  Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)

/-- **BG Appendix C**, the prime-field line `P₀ ≤ P`: the image in `P = 𝔽_{p^q}` of the additive
group of `𝔽_p`, i.e. the `𝔽_p`-span of `1`, viewed inside `H = P ⋊ U`. -/
noncomputable def primeLine (p q : ℕ) [Fact p.Prime] :
    Subgroup (NormSet.normOneFrobeniusGroup p q) :=
  NormSet.normOneFrobeniusSubspaceKernel p q
    (Submodule.span (ZMod p) ({(1 : GaloisField p q)} : Set (GaloisField p q)))

/-- **BG Appendix C, Hypothesis (B)** (p. 145), in the book's `p, q, G`-abstract form: no
Peterfalvi Section 16 configuration anywhere in the statement.

Verbatim: *"There is a monomorphism `σ : H → G`, a finite abelian `p'`-subgroup `Q` of `G`, and an
element `y ∈ Q` such that `σ(P₀)` normalizes `Q` and `σ(P₀)^y` normalizes `U`."*  Here
`H = P ⋊ U` is `NormSet.normOneFrobeniusGroup p q`, `P₀` is `primeLine p q`, and `U` is
identified with its image `σ(U)` inside `G` (Remark (VI)).

The conjugation is written `MulAut.conj y • σ(P₀) = y σ(P₀) y⁻¹`; since `Q` is a subgroup,
feeding it `y⁻¹` recovers the book's `σ(P₀)^y = y⁻¹ σ(P₀) y` verbatim, so the two readings define
the same hypothesis.

The concrete Peterfalvi Section 16 instance of (B) along the Feit--Thompson spine is
`OddOrder.Peterfalvi.S16.FieldNormalizerData`.  What is still missing to run Theorem C off the
abstract form is the implication *(B) ⟹ `hrel`* (BG Lemma C.3), currently available only through
Section 16; see issue 0151.

`hypothesisBAbstract_sl2` (in `OddOrder.BG.AppC_SL2Example`) is the book's Remark (II) witness,
showing this hypothesis is satisfiable (`p = 2`, `G = SL(2, 2^q)`). -/
structure HypothesisBAbstract (p q : ℕ) [Fact p.Prime] (G : Type*) [Group G] where
  /-- The monomorphism `σ : H = P ⋊ U → G`. -/
  sigma : NormSet.normOneFrobeniusGroup p q →* G
  /-- `σ` is a monomorphism. -/
  sigma_injective : Function.Injective sigma
  /-- The finite abelian `p'`-subgroup `Q ≤ G`. -/
  Q : Subgroup G
  /-- `Q` is finite. -/
  Q_finite : Finite Q
  /-- `Q` is abelian. -/
  Q_commutative : IsMulCommutative Q
  /-- `Q` is a `p'`-group. -/
  Q_pPrime : ¬ p ∣ Nat.card Q
  /-- The distinguished element `y ∈ Q`. -/
  y : G
  /-- `y` lies in `Q`. -/
  y_mem_Q : y ∈ Q
  /-- `σ(P₀)` normalizes `Q`. -/
  primeLine_normalizes_Q :
    (primeLine p q).map sigma ≤ Subgroup.normalizer (Q : Set G)
  /-- `σ(P₀)^y` normalizes `σ(U)`. -/
  primeLine_conj_normalizes_U :
    MulAut.conj y • ((primeLine p q).map sigma) ≤
      Subgroup.normalizer
        (((NormSet.normOneFrobeniusComplement p q).map sigma : Subgroup G) : Set G)

end OddOrder.BG.AppC
