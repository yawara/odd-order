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

/-- The `𝔽_p`-span of `1` in `𝔽_{p^q}` is the prime field, of cardinality `p`. -/
theorem card_span_singleton_one (p q : ℕ) [Fact p.Prime] :
    Nat.card (Submodule.span (ZMod p) ({(1 : GaloisField p q)} : Set (GaloisField p q))) = p := by
  have hinj : Function.Injective
      (LinearMap.toSpanSingleton (ZMod p) (GaloisField p q) 1) := by
    intro a b hab
    have : (algebraMap (ZMod p) (GaloisField p q)) a =
        (algebraMap (ZMod p) (GaloisField p q)) b := by
      simpa [LinearMap.toSpanSingleton_apply, Algebra.smul_def] using hab
    exact FaithfulSMul.algebraMap_injective (ZMod p) (GaloisField p q) this
  rw [LinearMap.span_singleton_eq_range]
  have : Nat.card (LinearMap.range (LinearMap.toSpanSingleton (ZMod p) (GaloisField p q) 1)) =
      Nat.card (ZMod p) := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
  rw [this, Nat.card_eq_fintype_card, ZMod.card]

/-- **`|P₀| = p`**: the prime-field line has order `p`.  This is what the Section 16 development
used to take from its own hypothesis (`p = |W₂|`); it is in fact a consequence of the setup, since
`P₀` is the image of the prime field `𝔽_p` inside `P = 𝔽_{p^q}`. -/
theorem card_primeLine (p q : ℕ) [Fact p.Prime] : Nat.card (primeLine p q) = p := by
  rw [primeLine, NormSet.normOneFrobeniusSubspaceKernel,
    Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
  exact card_span_singleton_one p q

/-- The element of the prime-field line `P₀ ≤ P ≤ H` corresponding to a scalar `c : ZMod p`,
i.e. `algebraMap c ∈ 𝔽_p ⊆ 𝔽_{p^q}` read inside the additive kernel. -/
noncomputable def primeLineElement (p q : ℕ) [Fact p.Prime] (c : ZMod p) :
    NormSet.normOneFrobeniusGroup p q :=
  SemidirectProduct.inl (Multiplicative.ofAdd (algebraMap (ZMod p) (GaloisField p q) c))

/-- The distinguished nonidentity element of the prime-field line `P₀`, corresponding to
`1 : 𝔽_{p^q}` in BG Appendix C. -/
noncomputable def primeLineGenerator (p q : ℕ) [Fact p.Prime] :
    NormSet.normOneFrobeniusGroup p q :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q))

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

/-! ## Hypothesis (B) with the three images named -/

section Data

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- **Field-normalizer data**: hypothesis (B) together with condition (A), with the three
subgroups `σ(P)`, `σ(U)`, `σ(P₀)` given names.

This is the shape in which the Lemma C.1--C.3 development consumes Theorem C's hypotheses: the
proofs constantly refer to the ambient subgroups `P = σ(P)`, `U = σ(U)` and `W₂ = σ(P₀)` of `G`,
so it is convenient to carry them as fields with their defining equations rather than to unfold
`Subgroup.map` everywhere.

The packaging adds **nothing**: `HypothesisBAbstract.toFieldNormalizerData` builds it from (B)
and (A) alone, taking the three subgroups to be literally the images (all three equations are
`rfl`).  So a `FieldNormalizerData` is exactly "(A) and (B)". -/
structure FieldNormalizerData (p q : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    extends HypothesisBAbstract p q G where
  /-- The image `P = σ(P)` of the additive kernel. -/
  P : Subgroup G
  /-- The image `U = σ(U)` of the norm-one complement. -/
  U : Subgroup G
  /-- The image `W₂ = σ(P₀)` of the prime-field line. -/
  W2 : Subgroup G
  /-- `P` is the image of the additive kernel. -/
  sigma_P_eq_P : (NormSet.normOneFrobeniusKernel p q).map sigma = P
  /-- `U` is the image of the norm-one complement. -/
  sigma_U_eq_U : (NormSet.normOneFrobeniusComplement p q).map sigma = U
  /-- `W₂` is the image of the prime-field line. -/
  sigma_P0_eq_W2 : (primeLine p q).map sigma = W2
  /-- `q` is prime (the standing hypothesis of Theorem C). -/
  q_prime : q.Prime
  /-- `p` is odd.  By **Remark (V)** ("by (A), we can assume `p` and `q` are odd") this costs
  nothing: `le_of_conditionA_of_not_odd` disposes of the even case outright. -/
  p_odd : Odd p
  /-- Condition (A). -/
  cyclotomic_coprime : conditionA p q

namespace FieldNormalizerData

/-- `W₂ = σ(P₀)` normalizes `Q`: clause (B) read through `sigma_P0_eq_W2`. -/
theorem W2_normalizes_Q (data : FieldNormalizerData p q G) :
    data.W2 ≤ Subgroup.normalizer (data.Q : Set G) := by
  rw [← data.sigma_P0_eq_W2]
  exact data.primeLine_normalizes_Q

/-- `2 ≠ 0` in `𝔽_p`, since `p` is odd. -/
theorem zmod_two_ne_zero (data : FieldNormalizerData p q G) : (2 : ZMod p) ≠ 0 := by
  intro hzero
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hdvd : (p : ℕ) ∣ 2 := by
    have h : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hzero
    exact (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 : p = 2 := le_antisymm hple (Fact.out : p.Prime).two_le
  rcases data.p_odd with ⟨k, hk⟩
  omega

/-- **`|W₂| = p`**: the transported prime line has order `p`, because `W₂ = σ(P₀)`, `σ` is
injective and `|P₀| = p` (`card_primeLine`).  The Section 16 development previously took this
from its own hypothesis field `p = |W₂|`; it is a consequence of (B). -/
theorem card_W2 (data : FieldNormalizerData p q G) : Nat.card data.W2 = p := by
  rw [← data.sigma_P0_eq_W2, Subgroup.card_map_of_injective data.sigma_injective]
  exact card_primeLine p q

/-- **A `p`-element of `Q` is trivial**, because `Q` is a `p'`-group.  This is all the Lemma C.3
development ever needs from `Q`'s order — the Section 16 route used to derive it from the
*stronger* "`Q` is elementary abelian of exponent `q`", but the book only assumes `Q` abelian
and `p'`. -/
theorem eq_one_of_mem_Q_of_pow_p_eq_one (data : FieldNormalizerData p q G)
    {x : G} (hx : x ∈ data.Q) (hxp : x ^ p = 1) : x = 1 := by
  have := data.Q_finite
  have hord : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) _ hord) with h1 | hp
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    refine data.Q_pPrime ?_
    have hsub : orderOf (⟨x, hx⟩ : data.Q) = orderOf x :=
      (orderOf_injective data.Q.subtype Subtype.val_injective ⟨x, hx⟩).symm
    have : orderOf (⟨x, hx⟩ : data.Q) ∣ Nat.card data.Q := orderOf_dvd_natCard _
    rw [hsub, hp] at this
    exact this

/-- `W₂^y` normalizes `U`: clause (B) read through `sigma_P0_eq_W2` and `sigma_U_eq_U`. -/
theorem W2_conj_y_normalizes_U (data : FieldNormalizerData p q G) :
    MulAut.conj data.y • data.W2 ≤ Subgroup.normalizer (data.U : Set G) := by
  rw [← data.sigma_P0_eq_W2, ← data.sigma_U_eq_U]
  exact data.primeLine_conj_normalizes_U

end FieldNormalizerData

/-- Hypothesis (B) together with condition (A) *is* field-normalizer data: take the three named
subgroups to be the images themselves.  This is what makes `FieldNormalizerData` a pure
repackaging rather than a strengthening. -/
noncomputable def HypothesisBAbstract.toFieldNormalizerData (hb : HypothesisBAbstract p q G)
    (hq : q.Prime) (hp_odd : Odd p) (hA : conditionA p q) : FieldNormalizerData p q G where
  toHypothesisBAbstract := hb
  P := (NormSet.normOneFrobeniusKernel p q).map hb.sigma
  U := (NormSet.normOneFrobeniusComplement p q).map hb.sigma
  W2 := (primeLine p q).map hb.sigma
  sigma_P_eq_P := rfl
  sigma_U_eq_U := rfl
  sigma_P0_eq_W2 := rfl
  q_prime := hq
  p_odd := hp_odd
  cyclotomic_coprime := hA

end Data

end OddOrder.BG.AppC
