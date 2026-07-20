/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven.TraceFormula
import OddOrder.Higman.Suzuki2Groups.HigmanFiniteFieldTrace
import OddOrder.Higman.Suzuki2Groups.HigmanSquareMap
import OddOrder.Higman.Suzuki2Groups.HigmanXiLengthTwo

/-!
# Higman's Lemma 11: excluding a proper field extension

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 11, p. 89.

This leaf formalizes the contradiction after the trace calculation.  The
xi-length-two structure makes the actual first-layer square map nonzero away
from zero, while Lemma 10 supplies a nonzero trace-zero coordinate in every
proper odd-degree field extension.  Therefore the relative degree is one.
-/

set_option autoImplicit false

open scoped IsMulCommutative
open OddOrder.GroupTheory

namespace OddOrder.Higman.Suzuki2Groups

universe u uK uL uW

local instance properExtensionLayerIsMulCommutative
    (P : Type u) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

/-! ## Nonvanishing of the actual square map -/

/-- If the second lower-central layer has trivial denominator and every
involution lies in the second lower-central term, the first-layer square map
has trivial zero locus. -/
theorem lowerCentralSquareMap_eq_one_imp_eq_one_of_kernel_one_eq_bot
    (H : Type u) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (hK1 : lowerCentralLayerKernel H 1 = ⊥)
    (hInv : ∀ x : H, x ^ 2 = 1 → x ∈ lowerCentralTerm H 1)
    (u : lowerCentralLayer H 0)
    (hu : lowerCentralSquareMap H hSq u = 1) :
    u = 1 := by
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel H 0) u
  have hsquareValue : lowerCentralSquareValue H hSq g = 1 := by
    simpa only [lowerCentralSquareMap_mk] using hu
  have hsquareRepMem : lowerCentralSquareRepresentative H hSq g ∈
      lowerCentralLayerKernel H 1 :=
    (QuotientGroup.eq_one_iff _).mp hsquareValue
  have hsquareRep : lowerCentralSquareRepresentative H hSq g = 1 := by
    rw [hK1] at hsquareRepMem
    exact Subgroup.mem_bot.mp hsquareRepMem
  have hgsq : (g : H) ^ 2 = 1 := congrArg Subtype.val hsquareRep
  apply (QuotientGroup.eq_one_iff g).mpr
  rw [lowerCentralLayerKernel_zero_eq_of_squares_le H hSq,
    Subgroup.mem_subgroupOf]
  exact hInv (g : H) hgsq

/-- Additive nonvanishing form of the preceding quotient-kernel criterion. -/
theorem lowerCentralSquareMapAdditive_ne_zero_of_kernel_one_eq_bot
    (H : Type u) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (hK1 : lowerCentralLayerKernel H 1 = ⊥)
    (hInv : ∀ x : H, x ^ 2 = 1 → x ∈ lowerCentralTerm H 1)
    (u : Additive (lowerCentralLayer H 0))
    (hu : u ≠ 0) :
    lowerCentralSquareMapAdditive H hSq u ≠ 0 := by
  intro hzero
  apply hu
  apply Additive.toMul.injective
  change Additive.toMul u = 1
  apply lowerCentralSquareMap_eq_one_imp_eq_one_of_kernel_one_eq_bot
    H hSq hK1 hInv
  apply Additive.ofMul.injective
  exact hzero

/-- Higman's nonabelian xi-length-two hypotheses imply the actual square map
is nonzero on every nonzero first-layer vector. -/
theorem lowerCentralSquareMapAdditive_ne_zero_of_xiLengthTwo
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (u : Additive (lowerCentralLayer P 0))
    (hu : u ≠ 0) :
    lowerCentralSquareMapAdditive P
        (lowerCentralSquaresLieInSecond_of_agemo_eq P
          (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)) u ≠ 0 := by
  have hcomm_ne : _root_.commutator P ≠ (⊥ : Subgroup P) :=
    fun h ↦ hncomm ((commutator_eq_bot_iff P).mp h)
  letI : Nontrivial (_root_.commutator P) :=
    (Subgroup.nontrivial_iff_ne_bot (_root_.commutator P)).mpr hcomm_ne
  letI : Nontrivial P :=
    (_root_.commutator P).subtype_injective.nontrivial
  let hSq := lowerCentralSquaresLieInSecond_of_agemo_eq P
    (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)
  have hAmbientK1 : lowerCentralLayerKernelInAmbient P 1 = ⊥ := by
    rw [lowerCentralLayerKernelInAmbient_eq,
      show 1 + 1 = 2 by omega,
      lowerCentralTerm_two_eq_bot hP hncomm hxi hlen, sup_bot_eq,
      lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      frattini_agemo_one_map_eq_bot hP hncomm hxi hlen]
  have hK1 : lowerCentralLayerKernel P 1 = ⊥ := by
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 1, hAmbientK1]
    simp
  have hInv : ∀ x : P, x ^ 2 = 1 → x ∈ lowerCentralTerm P 1 := by
    intro x hx
    rw [lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      frattini_eq_involutionSubgroup hP hncomm hxi hlen,
      involutionSubgroup, mem_omega1OfAbelian]
    refine ⟨?_, hx⟩
    by_cases hx1 : x = 1
    · simp [hx1]
    · exact involutions_subset_center_of_transitive hP Y hxi.transitive
        ⟨hx, hx1⟩
  exact lowerCentralSquareMapAdditive_ne_zero_of_kernel_one_eq_bot
    P hSq hK1 hInv u hu

/-! ## The Lemma 10 contradiction -/

/-- Minimal endgame connector for Higman's Lemma 11.

If the square map is given by the relative-trace normal form produced by the
single-gap calculation, and it is nonzero on every nonzero first-layer
coordinate, then the odd finite extension cannot be proper. -/
theorem finrank_eq_one_of_trace_squareMap_ne_zero
    {K : Type uK} {L : Type uL} {W : Type uW}
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [AddCommMonoid W]
    (q : L → W) (iotaAdd : K →+ W)
    (hodd : Odd (Module.finrank K L))
    (r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      q alpha = iotaAdd
        (Algebra.trace K L
          (alpha * alpha ^ (2 ^ r) * epsilon)))
    (hq_ne_zero : ∀ alpha : L, alpha ≠ 0 → q alpha ≠ 0) :
    Module.finrank K L = 1 := by
  have hnotProper : ¬ 1 < Module.finrank K L := by
    intro hproper
    obtain ⟨alpha, halpha, htrace⟩ :=
      higmanLemmaTen hproper hodd (r : Int) epsilon
    have hfrobenius :
        alpha ^ (2 ^ r) =
          ((frobeniusEquiv L 2) ^ (r : Int)) alpha := by
      rw [zpow_natCast, ← iterateFrobeniusEquiv_eq_pow]
      exact (iterateFrobeniusEquiv_def L 2 r alpha).symm
    have htraceNat :
        Algebra.trace K L
          (alpha * alpha ^ (2 ^ r) * epsilon) = 0 := by
      rw [hfrobenius]
      exact htrace
    apply hq_ne_zero alpha halpha
    rw [hformula alpha, htraceNat, map_zero]
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  omega

/-- Anchor-general variant.  Frobenius bijectivity pulls the witness from
Lemma 10 back through `alpha ↦ alpha^(2^a)`. -/
theorem finrank_eq_one_of_anchoredTrace_squareMap_ne_zero
    {K : Type uK} {L : Type uL} {W : Type uW}
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [AddCommMonoid W]
    (q : L → W) (iotaAdd : K →+ W)
    (hodd : Odd (Module.finrank K L))
    (a r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      q alpha = iotaAdd
        (Algebra.trace K L
          (alpha ^ (2 ^ a) *
            (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon)))
    (hq_ne_zero : ∀ alpha : L, alpha ≠ 0 → q alpha ≠ 0) :
    Module.finrank K L = 1 := by
  have hfrobenius (x : L) (t : Nat) :
      x ^ (2 ^ t) = ((frobeniusEquiv L 2) ^ (t : Int)) x := by
    rw [zpow_natCast, ← iterateFrobeniusEquiv_eq_pow]
    exact (iterateFrobeniusEquiv_def L 2 t x).symm
  have hnotProper : ¬ 1 < Module.finrank K L := by
    intro hproper
    obtain ⟨beta, hbeta, htrace⟩ :=
      higmanLemmaTen hproper hodd (r : Int) epsilon
    obtain ⟨alpha, halphaImage⟩ :=
      ((frobeniusEquiv L 2) ^ (a : Int)).surjective beta
    have hanchor : alpha ^ (2 ^ a) = beta :=
      (hfrobenius alpha a).trans halphaImage
    have halpha : alpha ≠ 0 := by
      intro halphaZero
      apply hbeta
      rw [← hanchor, halphaZero, zero_pow (by positivity)]
    have htraceNat :
        Algebra.trace K L
          (beta * beta ^ (2 ^ r) * epsilon) = 0 := by
      rw [hfrobenius beta r]
      exact htrace
    apply hq_ne_zero alpha halpha
    rw [hformula alpha, hanchor, htraceNat, map_zero]
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  omega

/-- **Higman Lemma 11 (p. 89), exclusion of a proper field extension.**

For a nonabelian xi-length-two group, an anchored trace formula for its actual
lower-central square map forces the relative first-layer field degree to be
one.  This is Higman's contradiction: Lemma 10 would otherwise produce a
nonzero first-layer coordinate whose square is zero, hence an involution
outside the Frattini subgroup. -/
theorem finrank_eq_one_of_anchoredTrace_lowerCentralSquareMap_of_xiLengthTwo
    {P : Type u} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    (e : Additive (lowerCentralLayer P 0) ≃+ L)
    (iotaAdd : K →+ Additive (lowerCentralLayer P 1))
    (hodd : Odd (Module.finrank K L))
    (a r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      lowerCentralSquareMapAdditive P
          (lowerCentralSquaresLieInSecond_of_agemo_eq P
            (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen))
          (e.symm alpha) =
        iotaAdd
          (Algebra.trace K L
            (alpha ^ (2 ^ a) *
              (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon))) :
    Module.finrank K L = 1 := by
  let hSq := lowerCentralSquaresLieInSecond_of_agemo_eq P
    (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)
  let q : L → Additive (lowerCentralLayer P 1) := fun alpha =>
    lowerCentralSquareMapAdditive P hSq (e.symm alpha)
  apply finrank_eq_one_of_anchoredTrace_squareMap_ne_zero
    q iotaAdd hodd a r epsilon
  · intro alpha
    exact hformula alpha
  · intro alpha halpha
    apply lowerCentralSquareMapAdditive_ne_zero_of_xiLengthTwo
      hP hncomm hxi hlen
    intro hzero
    apply halpha
    apply e.symm.injective
    simpa only [map_zero] using hzero

/-! ## The trace is superfluous in degree one -/

/-- The algebra map is a ring equivalence when the relative degree is one. -/
noncomputable def finrankOneRingEquiv
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Algebra K L]
    (hfin : Module.finrank K L = 1) : K ≃+* L :=
  RingEquiv.ofBijective (algebraMap K L)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin)

@[simp]
theorem finrankOneRingEquiv_apply
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Algebra K L]
    (hfin : Module.finrank K L = 1) (x : K) :
    finrankOneRingEquiv K L hfin x = algebraMap K L x :=
  rfl

/-- Over a degree-one extension of finite fields, embedding the relative trace
back into the top field returns the original element. -/
theorem algebraMap_trace_eq_self_of_finrank_eq_one
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Finite K] [Finite L] [Algebra K L]
    (hfin : Module.finrank K L = 1) (x : L) :
    algebraMap K L (Algebra.trace K L x) = x := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, hfin]
  simp

/-- Thus the relative trace itself is the inverse of the algebra-map
equivalence. -/
theorem trace_eq_finrankOneRingEquiv_symm
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Finite K] [Finite L] [Algebra K L]
    (hfin : Module.finrank K L = 1) (x : L) :
    Algebra.trace K L x = (finrankOneRingEquiv K L hfin).symm x := by
  let e := finrankOneRingEquiv K L hfin
  apply e.injective
  calc
    e (Algebra.trace K L x) =
        algebraMap K L (Algebra.trace K L x) := rfl
    _ = x := algebraMap_trace_eq_self_of_finrank_eq_one K L hfin x
    _ = e (e.symm x) := (e.apply_symm_apply x).symm

/-- Higman's absolute finite-field degrees agree when the relative degree is
one.  This is the equality `m = n` on p. 89. -/
theorem absoluteFinrank_eq_of_relativeFinrank_eq_one
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [Algebra (ZMod 2) K] [Algebra (ZMod 2) L]
    [IsScalarTower (ZMod 2) K L]
    (hfin : Module.finrank K L = 1) :
    Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) K := by
  rw [← Module.finrank_mul_finrank (ZMod 2) K L, hfin, mul_one]

/-- Named-degree form of Higman's conclusion `m = n`. -/
theorem absoluteDegrees_eq_of_relativeFinrank_eq_one
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [Algebra (ZMod 2) K] [Algebra (ZMod 2) L]
    [IsScalarTower (ZMod 2) K L]
    (m n : Nat)
    (hfinK : Module.finrank (ZMod 2) K = n)
    (hfinL : Module.finrank (ZMod 2) L = m)
    (hfin : Module.finrank K L = 1) :
    m = n := by
  calc
    m = Module.finrank (ZMod 2) L := hfinL.symm
    _ = Module.finrank (ZMod 2) K :=
      absoluteFinrank_eq_of_relativeFinrank_eq_one K L hfin
    _ = n := hfinK

/-- The exact right-hand-side rewrite in the anchored Frobenius-sum theorem:
the relative trace disappears after the relative degree has been proved one. -/
theorem anchoredFrobeniusSum_trace_superfluous
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Finite K] [Finite L] [Algebra K L]
    {M : Type uW} [AddCommMonoid M] [Module L M]
    (hfin : Module.finrank K L = 1)
    (n : Nat) (bTwo : Fin n → M) (s₀ : Fin n) (z : L) :
    (∑ s : Fin n,
        (algebraMap K L (Algebra.trace K L z)) ^ (2 ^ s.val) •
          bTwo (s₀ + s)) =
      ∑ s : Fin n, z ^ (2 ^ s.val) • bTwo (s₀ + s) := by
  rw [algebraMap_trace_eq_self_of_finrank_eq_one K L hfin z]

/-- Higman's p. 89 statement that the trace is superfluous.  A degree-one
anchored trace normal form is the same formula with an additive coordinate
map defined on the common field itself. -/
theorem anchoredTraceFormula_trace_superfluous
    {K : Type uK} {L : Type uL} {W : Type uW}
    [Field K] [Field L] [Finite K] [Finite L] [Algebra K L]
    [AddCommMonoid W]
    (hfin : Module.finrank K L = 1)
    (q : L → W) (iotaAdd : K →+ W)
    (a r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      q alpha = iotaAdd
        (Algebra.trace K L
          (alpha ^ (2 ^ a) *
            (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon))) :
    ∃ iotaL : L →+ W, ∀ alpha : L,
      q alpha = iotaL
        (alpha ^ (2 ^ a) *
          (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon) := by
  refine ⟨iotaAdd.comp
    (finrankOneRingEquiv K L hfin).symm.toAddMonoidHom, ?_⟩
  intro alpha
  change q alpha = iotaAdd
    ((finrankOneRingEquiv K L hfin).symm
      (alpha ^ (2 ^ a) *
        (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon))
  rw [hformula alpha,
    trace_eq_finrankOneRingEquiv_symm K L hfin]

end OddOrder.Higman.Suzuki2Groups
