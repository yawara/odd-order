/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven.ProperExtension
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types

/-!
# Higman's Lemma 11: the type-A conclusion

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 11, p. 89.

This leaf converts the two actual lower-central layers into kernel and
quotient coordinates for a central group extension.  It also absorbs the
nonzero scalar in Higman's square formula into the kernel coordinate and
feeds the resulting square map to Peterfalvi's concrete type-A model.
-/

set_option autoImplicit false

open scoped IsMulCommutative TensorProduct BigOperators
open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups
open Module

namespace OddOrder.Higman.Suzuki2Groups

universe uP uF uK uL uV uC

noncomputable section

local instance lowerCentralTermOneNormalForCoordinates
    (P : Type uP) [Group P] :
    (lowerCentralTerm P 1).Normal := by
  dsimp [lowerCentralTerm]
  infer_instance

local instance sourceSquareLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance sourceSquareLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance sourceSquareLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-! ## Actual Singer-basis inputs -/

/-- If a basis diagonalizes a generator of a finite cyclic group, it
diagonalizes every group element. -/
private theorem exists_cyclicActorWeight_of_generatorWeight
    {C : Type uC} {V : Type uV} {L : Type uL}
    [CommGroup C] [IsCyclic C] [Finite C]
    [AddCommGroup V] [Module (ZMod 2) V]
    [Field L] [Algebra (ZMod 2) L]
    (rho : Representation (ZMod 2) C V)
    {m : Nat} (b : Basis (Fin m) L (L ⊗[ZMod 2] V))
    (c : C) (hcgen : ∀ g : C, g ∈ Subgroup.zpowers c)
    (w : Fin m → L)
    (hc : ∀ i, (rho c).baseChange L (b i) = w i • b i) :
    ∃ weight : C → Fin m → L, ∀ g i,
      (rho g).baseChange L (b i) = weight g i • b i := by
  have hgpow : ∀ g : C, ∃ k : Nat, c ^ k = g := by
    intro g
    have hg : g ∈ Submonoid.powers c :=
      (isOfFinOrder_of_finite c).mem_powers_iff_mem_zpowers.mpr
        (hcgen g)
    exact hg
  have hpow : ∀ t : Nat, ∀ i,
      (rho (c ^ t)).baseChange L (b i) = w i ^ t • b i := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        intro i
        rw [pow_succ, map_mul, LinearMap.baseChange_mul]
        change (rho (c ^ t)).baseChange L
            ((rho c).baseChange L (b i)) = _
        rw [hc, map_smul, ih, smul_smul, pow_succ, mul_comm]
  choose k hk using hgpow
  let weight : C → Fin m → L := fun g i => w i ^ k g
  refine ⟨weight, ?_⟩
  intro g i
  have hi := hpow (k g) i
  rw [hk g] at hi
  simpa only [weight] using hi

/-- Reindex the canonical conjugate basis along an explicit absolute-degree
equality. -/
private noncomputable def canonicalFirstBasisReindexed
    {L : Type uL} {V : Type uV}
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] L) (N : Nat)
    (hfin : finrank (ZMod 2) L = N) :
    Basis (Fin N) L (L ⊗[ZMod 2] V) :=
  (conjugateTensorBasisOfLinearEquiv L e).reindex (finCongr hfin)

/-- The reindexed canonical basis retains its ground-vector expansion. -/
private theorem one_tmul_eq_sum_canonicalFirstBasisReindexed
    {L : Type uL} {V : Type uV}
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] L) (N : Nat)
    (hfin : finrank (ZMod 2) L = N)
    (v : V) :
    let b := canonicalFirstBasisReindexed e N hfin
    (1 : L) ⊗ₜ[ZMod 2] v =
      ∑ i : Fin N, (e v) ^ (2 ^ i.val) • b i := by
  subst N
  have hb : canonicalFirstBasisReindexed e
      (finrank (ZMod 2) L) rfl =
        conjugateTensorBasisOfLinearEquiv L e := by
    simp [canonicalFirstBasisReindexed]
  rw [hb]
  exact one_tmul_eq_sum_conjugateTensorBasisOfLinearEquiv L e v

/-- The reindexed canonical first-layer basis retains its Frobenius cycle. -/
private theorem frobeniusScalarBaseChange_canonicalFirstBasisReindexed
    {L : Type uL} {V : Type uV}
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] L) (N : Nat)
    (hfin : finrank (ZMod 2) L = N)
    (i : Fin N) :
    let b := canonicalFirstBasisReindexed e N hfin
    frobeniusScalarBaseChange L (b i) =
      b (higmanCyclicSucc (hfin ▸ finrank_pos) i) := by
  subst N
  have hb : canonicalFirstBasisReindexed e
      (finrank (ZMod 2) L) rfl =
        conjugateTensorBasisOfLinearEquiv L e := by
    simp [canonicalFirstBasisReindexed]
  rw [hb]
  have h :=
    frobeniusScalarBaseChange_conjugateTensorBasisAlongOfLinearEquiv
      L L (AlgHom.id (ZMod 2) L) e i
  change frobeniusScalarBaseChange L
      (conjugateTensorBasisOfLinearEquiv L e i) =
    conjugateTensorBasisOfLinearEquiv L e
      (higmanCyclicSucc finrank_pos i) at h
  exact h

/-- A normalized generator eigenvalue gives the expected Frobenius weights
on the reindexed canonical basis. -/
private theorem generator_baseChange_canonicalFirstBasisReindexed
    {L : Type uL} {V : Type uV} {C : Type uC}
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [AddCommGroup V] [Module (ZMod 2) V] [Group C]
    (rho : Representation (ZMod 2) C V) (c : C)
    (e : V ≃ₗ[ZMod 2] L) (lambda : L)
    (hcompat : ∀ v, e (rho c v) = lambda * e v)
    (N : Nat) (hfin : finrank (ZMod 2) L = N)
    (i : Fin N) :
    let b := canonicalFirstBasisReindexed e N hfin
    (rho c).baseChange L (b i) =
      lambda ^ (2 ^ i.val) • b i := by
  subst N
  have hb : canonicalFirstBasisReindexed e
      (finrank (ZMod 2) L) rfl =
        conjugateTensorBasisOfLinearEquiv L e := by
    simp [canonicalFirstBasisReindexed]
  rw [hb]
  exact baseChange_eigen_conjugateTensorBasisOfLinearEquiv
    L e (rho c) lambda hcompat i

/-- The actual lower-central square map has Higman's pairwise Frobenius
expansion in the reindexed canonical first-layer basis. -/
private theorem lowerCentralSquareMapBaseChange_eq_frobeniusSum_of_generator
    {L : Type uL} {H C : Type uP}
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [Group H] [Finite H]
    [CommGroup C] [IsCyclic C] [Finite C]
    (phi : C →* MulAut H)
    (hSq : LowerCentralSquaresLieInSecond H)
    (n : Nat) (hn : 2 ≤ n)
    (hfinTwo : finrank (ZMod 2)
      (Additive (lowerCentralLayer H 1)) = n)
    (hirrOne : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (hfaithOne : Function.Injective
      (lowerCentralLayerRepresentation phi 0))
    (htransTwo : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ g : C,
        lowerCentralLayerRepresentation phi 1 g v = w)
    (eOne : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] L)
    (N : Nat) (hfinOne : finrank (ZMod 2) L = N)
    (c : C) (hcgen : ∀ g : C, g ∈ Subgroup.zpowers c)
    (lambda : L)
    (hcompat : ∀ v,
      eOne (lowerCentralLayerRepresentation phi 0 c v) =
        lambda * eOne v) :
    let bOne := canonicalFirstBasisReindexed eOne N hfinOne
    ∀ x : Additive (lowerCentralLayer H 0),
      lowerCentralSquareMapBaseChange L H hSq x =
        ∑ i : Fin N, ∑ j : Fin N with i < j,
          (eOne x) ^ (2 ^ i.val + 2 ^ j.val) •
            lowerCentralCommutatorBilinearBaseChange L H
              (bOne i) (bOne j) := by
  dsimp only
  let bOne := canonicalFirstBasisReindexed eOne N hfinOne
  have hcEigen : ∀ i,
      (lowerCentralLayerRepresentation phi 0 c).baseChange L (bOne i) =
        lambda ^ (2 ^ i.val) • bOne i := by
    exact generator_baseChange_canonicalFirstBasisReindexed
      (lowerCentralLayerRepresentation phi 0) c eOne lambda hcompat
      N hfinOne
  obtain ⟨weight, hweight⟩ :=
    exists_cyclicActorWeight_of_generatorWeight
      (lowerCentralLayerRepresentation phi 0) bOne c hcgen
      (fun i => lambda ^ (2 ^ i.val)) hcEigen
  have hActual :
      lowerCentralSquareMapBaseChange L H hSq =
        lowerCentralUpperQuadraticCandidate L bOne :=
    lowerCentralSquareMapBaseChange_eq_upperQuadraticCandidate
      (H := H) (C := C) L phi hSq
      n hn hfinTwo hirrOne hfaithOne htransTwo bOne weight hweight
  intro x
  calc
    lowerCentralSquareMapBaseChange L H hSq x =
        lowerCentralUpperQuadraticCandidate L bOne x :=
      congrFun hActual x
    _ = upperQuadraticMap bOne
        (lowerCentralCommutatorBilinearBaseChange L H)
        (∑ i : Fin N, (eOne x) ^ (2 ^ i.val) • bOne i) := by
      simp only [lowerCentralUpperQuadraticCandidate]
      rw [← one_tmul_eq_sum_canonicalFirstBasisReindexed
        eOne N hfinOne x]
    _ = ∑ i : Fin N, ∑ j : Fin N with i < j,
        (eOne x) ^ (2 ^ i.val + 2 ^ j.val) •
          lowerCentralCommutatorBilinearBaseChange L H
            (bOne i) (bOne j) :=
      upperQuadraticMap_apply_frobenius_sum bOne
        (lowerCentralCommutatorBilinearBaseChange L H) (eOne x)

/-- The canonical second-layer basis along an embedding is cycled by scalar
Frobenius. -/
private theorem frobeniusScalarBaseChange_canonicalSecondBasis
    {K : Type uK} {L : Type uL} {V : Type uV}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [AddCommGroup V] [Module (ZMod 2) V]
    (iota : K →ₐ[ZMod 2] L) (eTwo : V ≃ₗ[ZMod 2] K)
    (i : Fin (finrank (ZMod 2) K)) :
    frobeniusScalarBaseChange L
        (conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo i) =
      conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo
        (higmanCyclicSucc finrank_pos i) := by
  have h :=
    frobeniusScalarBaseChange_conjugateTensorBasisAlongOfLinearEquiv
      K L iota eTwo i
  change frobeniusScalarBaseChange L
      (conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo i) =
    conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo
      (higmanCyclicSucc finrank_pos i) at h
  exact h

/-! ## The Frobenius automorphism in the type-A model -/

private def ringAutMulEquivAlgAut
    (F : Type*) [Field F] (p : Nat) [Fact p.Prime]
    [Algebra (ZMod p) F] :
    RingAut F ≃* (F ≃ₐ[ZMod p] F) where
  toFun f := AlgEquiv.ofRingEquiv (f := f) fun x => by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    simp
  invFun g := g.toRingEquiv
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The ring Frobenius has the expected order over the prime field. -/
private theorem orderOf_frobeniusEquiv_eq_finrank
    {F : Type*} [Field F] [Finite F]
    (p : Nat) [Fact p.Prime] [CharP F p] [Algebra (ZMod p) F] :
    orderOf (frobeniusEquiv F p) = Module.finrank (ZMod p) F := by
  let toAlg := ringAutMulEquivAlgAut F p
  have hmap : toAlg (frobeniusEquiv F p) =
      FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F := by
    ext x
    change x ^ p = x ^ Fintype.card (ZMod p)
    rw [ZMod.card]
  calc
    orderOf (frobeniusEquiv F p) =
        orderOf (toAlg (frobeniusEquiv F p)) :=
      (orderOf_injective toAlg.toMonoidHom toAlg.injective _).symm
    _ = orderOf
        (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F) := by
      rw [hmap]
    _ = Module.finrank (ZMod p) F :=
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) F

/-- Cardinal coordinates identify the order of Frobenius with the displayed
finite-field degree. -/
theorem orderOf_frobeniusEquiv_eq_of_card_eq_two_pow
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : Nat) (hcard : Nat.card F = 2 ^ n) :
    orderOf (frobeniusEquiv F 2) = n := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  rw [orderOf_frobeniusEquiv_eq_finrank 2]
  apply Nat.pow_right_injective (by omega : 2 ≤ 2)
  calc
    2 ^ Module.finrank (ZMod 2) F = Nat.card F := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)).symm
    _ = 2 ^ n := hcard

/-- Every Frobenius power has odd order when the field degree is odd. -/
theorem frobeniusPower_orderOf_odd_of_card_eq_two_pow
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n r : Nat) (hcard : Nat.card F = 2 ^ n) (hnodd : Odd n) :
    Odd (orderOf ((frobeniusEquiv F 2) ^ r)) := by
  have hdvd := orderOf_pow_dvd (x := frobeniusEquiv F 2) r
  rw [orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard] at hdvd
  exact hnodd.of_dvd_nat hdvd

/-- A nonzero exponent strictly below the field degree gives a nontrivial
Frobenius power. -/
theorem frobeniusPower_ne_one_of_fin
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : Nat} [NeZero n]
    (hcard : Nat.card F = 2 ^ n) (r : Fin n) (hr : r ≠ 0) :
    (frobeniusEquiv F 2) ^ r.val ≠ 1 := by
  intro hphi
  have hdvdOrder : orderOf (frobeniusEquiv F 2) ∣ r.val :=
    orderOf_dvd_iff_pow_eq_one.mpr hphi
  have hdvd : n ∣ r.val := by
    simpa only [orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard]
      using hdvdOrder
  have hrzero : r.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd r.isLt
  apply hr
  apply Fin.ext
  simpa using hrzero

/-- For odd modulus, `r + r ≠ 0` follows from `r ≠ 0`. -/
theorem fin_add_self_ne_zero_of_odd
    {n : Nat} [NeZero n] (hnodd : Odd n)
    (r : Fin n) (hr : r ≠ 0) :
    r + r ≠ 0 := by
  intro hrr
  have hmod : n ∣ 2 * r.val := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hval := congrArg Fin.val hrr
    simpa [Fin.val_add, two_mul] using hval
  have hnCoprime : n.Coprime 2 :=
    Nat.coprime_two_right.mpr hnodd
  have hdvd : n ∣ r.val := hnCoprime.dvd_of_dvd_mul_left hmod
  have hrzero : r.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd r.isLt
  apply hr
  apply Fin.ext
  simpa using hrzero

/-- A primitive Frobenius-shifted eigenvalue forces the relevant Frobenius
power to be nontrivial and to have odd order. -/
private theorem frobeniusPower_ne_one_and_orderOf_odd_of_primitive_shift
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    {n : Nat} [NeZero n]
    (hcard : Nat.card F = 2 ^ n)
    (lambda : F) (r : Fin n) (hr : r ≠ 0)
    (hshift : IsPrimitiveRoot
      (lambda ^ (1 + 2 ^ r.val)) (2 ^ n - 1)) :
    (frobeniusEquiv F 2) ^ r.val ≠ 1 ∧
      Odd (orderOf ((frobeniusEquiv F 2) ^ r.val)) := by
  have hnpos : 0 < n := NeZero.pos n
  refine ⟨frobeniusPower_ne_one_of_fin hcard r hr, ?_⟩
  have hmodpos : 0 < 2 ^ n - 1 := by
    have : 1 < 2 ^ n := one_lt_pow₀ (by omega) hnpos.ne'
    omega
  have hlambdaNe : lambda ≠ 0 := by
    intro hlambda
    have hone := hshift.pow_eq_one
    simp [hlambda, hmodpos.ne'] at hone
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hlambdaPeriod : lambda ^ (2 ^ n - 1) = 1 := by
    rw [← hcardF]
    exact FiniteField.pow_card_sub_one_eq_one lambda hlambdaNe
  have hlambdaOrderDvd : orderOf lambda ∣ 2 ^ n - 1 :=
    orderOf_dvd_of_pow_eq_one hlambdaPeriod
  have hmodDvdLambdaOrder : 2 ^ n - 1 ∣ orderOf lambda := by
    calc
      2 ^ n - 1 = orderOf (lambda ^ (1 + 2 ^ r.val)) :=
        hshift.eq_orderOf
      _ ∣ orderOf lambda := orderOf_pow_dvd _
  have hlambdaOrder : orderOf lambda = 2 ^ n - 1 :=
    Nat.dvd_antisymm hlambdaOrderDvd hmodDvdLambdaOrder
  have hlambdaPrimitive : IsPrimitiveRoot lambda (2 ^ n - 1) :=
    IsPrimitiveRoot.iff_orderOf.mpr hlambdaOrder
  have hcop : Nat.Coprime (1 + 2 ^ r.val) (2 ^ n - 1) :=
    (hlambdaPrimitive.pow_iff_coprime hmodpos
      (1 + 2 ^ r.val)).mp hshift
  have hquotientOdd : Odd (n / Nat.gcd r.val n) := by
    have hgcd := higmanPowerMapGcd r.val n hnpos
    rw [hcop.gcd_eq_one] at hgcd
    by_contra hnotOdd
    rw [if_neg hnotOdd] at hgcd
    have : 0 < 2 ^ Nat.gcd r.val n := by positivity
    omega
  letI : Finite (RingAut F) :=
    Finite.of_injective (fun sigma : RingAut F => (sigma : F → F))
      DFunLike.coe_injective
  rw [orderOf_pow,
    orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard]
  simpa only [Nat.gcd_comm] using hquotientOdd

/-! ## Actual lower-central extension coordinates -/

/-- The zeroth lower-central term is the ambient group.  Public because
Lemma 12's ambient `F × F` coordinate reuses this generic bridge
(`AmbientProductCoordinate`). -/
noncomputable def lowerCentralTermZeroEquivAmbient
    (P : Type uP) [Group P] :
    lowerCentralTerm P 0 ≃* P :=
  (MulEquiv.subgroupCongr (by simp [lowerCentralTerm])).trans
    Subgroup.topEquiv

/-- Under the square-layer identity, the ambient first lower-central term
maps to the kernel defining the zeroth lower-central layer. -/
private theorem lowerCentralTerm_one_map_zeroEquiv_symm
    (P : Type uP) [Group P]
    (hK0 : lowerCentralLayerKernel P 0 =
      (lowerCentralTerm P 1).subgroupOf (lowerCentralTerm P 0)) :
    (lowerCentralTerm P 1).map
        (lowerCentralTermZeroEquivAmbient P).symm =
      lowerCentralLayerKernel P 0 := by
  rw [hK0]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [lowerCentralTermZeroEquivAmbient, Subgroup.mem_subgroupOf] using hy
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    refine ⟨(x : P), hx, ?_⟩
    apply Subtype.ext
    rfl

/-- Identify the ambient quotient by the first lower-central term with the
actual zeroth lower-central layer. -/
private noncomputable def ambientQuotientEquivLowerCentralLayerZero
    (P : Type uP) [Group P]
    (hK0 : lowerCentralLayerKernel P 0 =
      (lowerCentralTerm P 1).subgroupOf (lowerCentralTerm P 0)) :
    P ⧸ lowerCentralTerm P 1 ≃* lowerCentralLayer P 0 :=
  QuotientGroup.congr _ _
    (lowerCentralTermZeroEquivAmbient P).symm
    (lowerCentralTerm_one_map_zeroEquiv_symm P hK0)

/-- When the second-layer denominator is trivial, the second layer is the
actual first lower-central term. -/
private noncomputable def lowerCentralLayerOneEquivTerm
    {P : Type uP} [Group P]
    (hK1 : lowerCentralLayerKernel P 1 = ⊥) :
    lowerCentralLayer P 1 ≃* lowerCentralTerm P 1 :=
  (QuotientGroup.quotientMulEquivOfEq hK1).trans
    QuotientGroup.quotientBot

/-- Kernel coordinates induced by an additive second-layer coordinate. -/
private noncomputable def lowerCentralExtensionLeft
    {P : Type uP} [Group P]
    {F : Type uF} [AddGroup F]
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (eOne : Additive (lowerCentralLayer P 1) ≃+ F) :
    Multiplicative F ≃* lowerCentralTerm P 1 :=
  (AddEquiv.toMultiplicativeLeft eOne.symm).trans
    (lowerCentralLayerOneEquivTerm hK1)

/-- Quotient coordinates induced by an additive zeroth-layer coordinate. -/
private noncomputable def lowerCentralExtensionRight
    {P : Type uP} [Group P]
    {F : Type uF} [AddGroup F]
    (hK0 : lowerCentralLayerKernel P 0 =
      (lowerCentralTerm P 1).subgroupOf (lowerCentralTerm P 0))
    (eZero : Additive (lowerCentralLayer P 0) ≃+ F) :
    P ⧸ lowerCentralTerm P 1 ≃* Multiplicative F :=
  (ambientQuotientEquivLowerCentralLayerZero P hK0).trans
    (AddEquiv.toMultiplicativeRight eZero)

/-- The kernel coordinate sends an actual second-layer square class back to
the ambient square. -/
private theorem lowerCentralExtensionLeft_square
    {P : Type uP} [Group P]
    {F : Type uF} [AddGroup F]
    (hSq : LowerCentralSquaresLieInSecond P)
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (eOne : Additive (lowerCentralLayer P 1) ≃+ F)
    (x : lowerCentralTerm P 0) :
    (x : P) ^ 2 = lowerCentralExtensionLeft hK1 eOne
      (Multiplicative.ofAdd
        (eOne (lowerCentralSquareMapAdditive P hSq
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x))))) := by
  change (x : P) ^ 2 =
    (((QuotientGroup.quotientMulEquivOfEq hK1).trans
      QuotientGroup.quotientBot)
      (Additive.toMul
        (eOne.symm
          (eOne (lowerCentralSquareMapAdditive P hSq
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x)))))) :
        lowerCentralTerm P 1)
  rw [eOne.symm_apply_apply, lowerCentralSquareMapAdditive_mk]
  rfl

/-- Xi-length two and additive coordinates on the two actual lower-central
layers produce the multiplicative kernel and quotient coordinates required by
`GroupExtension.ofNormalSubgroupCoordinates`. -/
theorem exists_lowerCentralExtensionCoordinates_of_xiLengthTwo
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    {F : Type uF} [AddGroup F]
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (eZero : Additive (lowerCentralLayer P 0) ≃+ F)
    (eOne : Additive (lowerCentralLayer P 1) ≃+ F) :
    ∃ (left : Multiplicative F ≃* lowerCentralTerm P 1)
      (right : P ⧸ lowerCentralTerm P 1 ≃* Multiplicative F),
      (GroupExtension.ofNormalSubgroupCoordinates
        (lowerCentralTerm P 1) left right).inl.range =
          lowerCentralTerm P 1 := by
  have hSq : LowerCentralSquaresLieInSecond P :=
    lowerCentralSquaresLieInSecond_of_agemo_eq P
      (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)
  have hK0 : lowerCentralLayerKernel P 0 =
      (lowerCentralTerm P 1).subgroupOf (lowerCentralTerm P 0) :=
    lowerCentralLayerKernel_zero_eq_of_squares_le P hSq
  have hAmbientK1 : lowerCentralLayerKernelInAmbient P 1 = ⊥ := by
    rw [lowerCentralLayerKernelInAmbient_eq,
      show 1 + 1 = 2 by omega,
      lowerCentralTerm_two_eq_bot hP hncomm hxi hlen, sup_bot_eq,
      lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      frattini_agemo_one_map_eq_bot hP hncomm hxi hlen]
  have hK1 : lowerCentralLayerKernel P 1 = ⊥ := by
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 1, hAmbientK1]
    simp
  let left : Multiplicative F ≃* lowerCentralTerm P 1 :=
    lowerCentralExtensionLeft hK1 eOne
  let right : P ⧸ lowerCentralTerm P 1 ≃* Multiplicative F :=
    lowerCentralExtensionRight hK0 eZero
  exact ⟨left, right,
    GroupExtension.ofNormalSubgroupCoordinates_range_inl
      (lowerCentralTerm P 1) left right⟩

/-! ## Absorbing the nonzero square coefficient -/

/-- Absorb the nonzero scalar in a type-A square formula into the kernel
coordinate of the central extension. -/
noncomputable def typeADataOfScaledSquareCoordinates
    {P : Type uP} [Group P]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (parameter : Nat) (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (phi : RingAut F) (phi_ne_one : phi ≠ 1)
    (phi_orderOf_odd : Odd (orderOf phi))
    (N : Subgroup P) [N.Normal]
    (left : Multiplicative F ≃* N)
    (right : P ⧸ N ≃* Multiplicative F)
    (hcentral : N ≤ Subgroup.center P)
    (epsilon : F) (hepsilon : epsilon ≠ 0)
    (hsq : ∀ x : P, x ^ 2 =
      left (Multiplicative.ofAdd
        (epsilon *
          ((right (QuotientGroup.mk' N x)).toAdd *
            phi (right (QuotientGroup.mk' N x)).toAdd)))) :
    TypeAData P := by
  let epsilonUnit : Fˣ := Units.mk0 epsilon hepsilon
  let scaleAdd : F ≃+ F :=
    (epsilonUnit.mulLeftLinearEquiv F F).toAddEquiv
  let scale : Multiplicative F ≃* Multiplicative F :=
    AddEquiv.toMultiplicative scaleAdd
  let left' : Multiplicative F ≃* N := scale.trans left
  let S : GroupExtension (Multiplicative F) P (Multiplicative F) :=
    GroupExtension.ofNormalSubgroupCoordinates N left' right
  apply TypeAData.ofExtension parameter parameter_pos card_field
    phi phi_ne_one phi_orderOf_odd S
  · simpa only [S, GroupExtension.ofNormalSubgroupCoordinates_range_inl]
      using hcentral
  · intro x
    rw [hsq x]
    rfl

/-! ## The actual anchored trace with an explicit first-layer index -/

/-- Index-flexible form of the actual anchored-trace connector. -/
private theorem
    exists_lowerCentralSquareMap_eq_anchoredTrace_of_actualSingerData_indexed_with_secondShift
    {P : Type uP} [Group P] [Finite P]
    (hAgemo : Agemo P 2 1 = lowerCentralTerm P 1)
    {K : Type uK} {L : Type uL}
    [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [CharP L 2] [Algebra (ZMod 2) L]
    [Algebra K L]
    (iota : K →ₐ[ZMod 2] L)
    (hiota : ∀ z : K, iota z = algebraMap K L z)
    (m d : Nat)
    [NeZero (finrank (ZMod 2) K)]
    [NeZero m]
    (hm : m = d * finrank (ZMod 2) K)
    (hn : 0 < finrank (ZMod 2) K) (hd : 0 < d)
    (hcardK : Nat.card K = 2 ^ finrank (ZMod 2) K)
    (hfinKL : finrank K L = d)
    (hfinL : finrank (ZMod 2) L = m)
    (eOne : Additive (lowerCentralLayer P 0) ≃ₗ[ZMod 2] L)
    (bOne : Basis (Fin m) L
      (L ⊗[ZMod 2] Additive (lowerCentralLayer P 0)))
    (hq : ∀ x,
      lowerCentralSquareMapBaseChange L P
          (lowerCentralSquaresLieInSecond_of_agemo_eq P hAgemo) x =
        ∑ i : Fin m, ∑ j : Fin m with i < j,
          (eOne x) ^ (2 ^ i.val + 2 ^ j.val) •
            lowerCentralCommutatorBilinearBaseChange L P
              (bOne i) (bOne j))
    (hcycleOne : ∀ i,
      frobeniusScalarBaseChange L (bOne i) =
        bOne (higmanCyclicSucc (hfinL ▸ finrank_pos) i))
    (eTwo : Additive (lowerCentralLayer P 1) ≃ₗ[ZMod 2] K)
    (bTwo : Basis (Fin (finrank (ZMod 2) K)) L
      (L ⊗[ZMod 2] Additive (lowerCentralLayer P 1)))
    (hbTwo : bTwo =
      conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo)
    (hcycleTwo : ∀ s,
      frobeniusScalarBaseChange L (bTwo s) =
        bTwo (higmanCyclicSucc hn s))
    (a : Fin m)
    (s₀ : Fin (finrank (ZMod 2) K))
    (r : Fin m)
    (hr0 : r ≠ 0) (hrtwo : r + r ≠ 0)
    (epsilon : L)
    (hseed : lowerCentralCommutatorBilinearBaseChange L P
        (bOne a) (bOne (a + r)) = epsilon • bTwo s₀)
    (hsymm : ∀ i j,
      lowerCentralCommutatorBilinearBaseChange L P
          (bOne i) (bOne j) =
        lowerCentralCommutatorBilinearBaseChange L P
          (bOne j) (bOne i))
    (hsupport : ∀ i j,
      j ≠ i + r → i ≠ j + r →
        lowerCentralCommutatorBilinearBaseChange L P
          (bOne i) (bOne j) = 0) :
    ∃ eTwoShift : Additive (lowerCentralLayer P 1) ≃ₗ[ZMod 2] K,
      eTwoShift = eTwo.trans
        (((FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod 2) K) ^ s₀.val).toLinearEquiv) ∧
      ∀ alpha : L,
        lowerCentralSquareMapAdditive P
            (lowerCentralSquaresLieInSecond_of_agemo_eq P hAgemo)
            (eOne.symm alpha) =
          eTwoShift.symm
            (Algebra.trace K L
              (alpha ^ (2 ^ a.val) *
                (alpha ^ (2 ^ a.val)) ^ (2 ^ r.val) * epsilon)) := by
  subst m
  exact exists_lowerCentralSquareMap_eq_anchoredTrace_of_actualSingerData_with_secondShift
    hAgemo iota hiota d hn hd hcardK hfinKL hfinL
    eOne bOne hq hcycleOne eTwo bTwo hbTwo hcycleTwo
    a s₀ r hr0 hrtwo epsilon hseed hsymm hsupport

/-! ## From the anchored trace formula to the square normal form -/

/-- A degree-one anchored trace formula for the actual lower-central square
map becomes the type-A square normal form after changing the first-layer
coordinate by the anchor Frobenius. -/
theorem exists_lowerCentralCoordinates_typeANormalForm_of_anchoredTrace_finrankOne
    {P : Type uP} [Group P]
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    (hfin : Module.finrank K L = 1)
    (hSq : LowerCentralSquaresLieInSecond P)
    (eZero : Additive (lowerCentralLayer P 0) ≃+ L)
    (eOneK : Additive (lowerCentralLayer P 1) ≃+ K)
    (a r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      lowerCentralSquareMapAdditive P hSq (eZero.symm alpha) =
        eOneK.symm
          (Algebra.trace K L
            (alpha ^ (2 ^ a) *
              (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon))) :
    ∃ eZero' : Additive (lowerCentralLayer P 0) ≃+ L,
      ∃ eOneL : Additive (lowerCentralLayer P 1) ≃+ L,
        ∀ beta : L,
          eOneL
              (lowerCentralSquareMapAdditive P hSq
                (eZero'.symm beta)) =
            epsilon *
              (beta * ((frobeniusEquiv L 2) ^ r) beta) := by
  let anchor : RingAut L := (frobeniusEquiv L 2) ^ a
  let eZero' : Additive (lowerCentralLayer P 0) ≃+ L :=
    eZero.trans anchor.toAddEquiv
  let eOneL : Additive (lowerCentralLayer P 1) ≃+ L :=
    eOneK.trans (finrankOneRingEquiv K L hfin).toAddEquiv
  refine ⟨eZero', eOneL, ?_⟩
  intro beta
  let alpha : L := anchor.symm beta
  have hfrobenius (x : L) (t : Nat) :
      x ^ (2 ^ t) = ((frobeniusEquiv L 2) ^ t) x := by
    rw [← iterateFrobeniusEquiv_eq_pow]
    exact (iterateFrobeniusEquiv_def L 2 t x).symm
  have hanchor : alpha ^ (2 ^ a) = beta := by
    rw [hfrobenius]
    exact anchor.apply_symm_apply beta
  calc
    eOneL
          (lowerCentralSquareMapAdditive P hSq
            (eZero'.symm beta)) =
        algebraMap K L
          (Algebra.trace K L
            (alpha ^ (2 ^ a) *
              (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon)) := by
      change algebraMap K L
          (eOneK
            (lowerCentralSquareMapAdditive P hSq
              (eZero.symm (anchor.symm beta)))) = _
      rw [hformula alpha]
      simp only [AddEquiv.apply_symm_apply]
    _ = alpha ^ (2 ^ a) *
          (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon :=
      algebraMap_trace_eq_self_of_finrank_eq_one K L hfin _
    _ = epsilon *
          (beta * ((frobeniusEquiv L 2) ^ r) beta) := by
      rw [hanchor, hfrobenius]
      ac_rfl

/-- A degree-one anchored trace formula can instead be normalized over the
kernel field while leaving a prescribed kernel coordinate unchanged.  Only
the quotient coordinate is transported: first by the anchor Frobenius on
`L`, then back along the degree-one field equivalence `K ≃+* L`. -/
theorem exists_lowerCentralQuotientCoordinate_typeANormalForm_of_anchoredTrace_finrankOne
    {P : Type uP} [Group P]
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    (hfin : Module.finrank K L = 1)
    (hSq : LowerCentralSquaresLieInSecond P)
    (eZero : Additive (lowerCentralLayer P 0) ≃+ L)
    (eKernel : Additive (lowerCentralLayer P 1) ≃+ K)
    (a r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      lowerCentralSquareMapAdditive P hSq (eZero.symm alpha) =
        eKernel.symm
          (Algebra.trace K L
            (alpha ^ (2 ^ a) *
              (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon))) :
    ∃ eZeroK : Additive (lowerCentralLayer P 0) ≃+ K,
      ∀ beta : K,
        eKernel
            (lowerCentralSquareMapAdditive P hSq
              (eZeroK.symm beta)) =
          (finrankOneRingEquiv K L hfin).symm epsilon *
            (beta * ((frobeniusEquiv K 2) ^ r) beta) := by
  let anchor : RingAut L := (frobeniusEquiv L 2) ^ a
  let fieldEquiv : K ≃+* L := finrankOneRingEquiv K L hfin
  let eZeroK : Additive (lowerCentralLayer P 0) ≃+ K :=
    (eZero.trans anchor.toAddEquiv).trans fieldEquiv.symm.toAddEquiv
  refine ⟨eZeroK, ?_⟩
  intro beta
  let alpha : L := anchor.symm (fieldEquiv beta)
  have hfrobeniusL (x : L) (t : Nat) :
      x ^ (2 ^ t) = ((frobeniusEquiv L 2) ^ t) x := by
    rw [← iterateFrobeniusEquiv_eq_pow]
    exact (iterateFrobeniusEquiv_def L 2 t x).symm
  have hfrobeniusK (x : K) (t : Nat) :
      x ^ (2 ^ t) = ((frobeniusEquiv K 2) ^ t) x := by
    rw [← iterateFrobeniusEquiv_eq_pow]
    exact (iterateFrobeniusEquiv_def K 2 t x).symm
  have hanchor : alpha ^ (2 ^ a) = fieldEquiv beta := by
    rw [hfrobeniusL]
    exact anchor.apply_symm_apply (fieldEquiv beta)
  calc
    eKernel
          (lowerCentralSquareMapAdditive P hSq
            (eZeroK.symm beta)) =
        Algebra.trace K L
          (alpha ^ (2 ^ a) *
            (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon) := by
      change eKernel
          (lowerCentralSquareMapAdditive P hSq
            (eZero.symm (anchor.symm (fieldEquiv beta)))) = _
      rw [hformula alpha]
      simp only [AddEquiv.apply_symm_apply]
    _ = fieldEquiv.symm
          (alpha ^ (2 ^ a) *
            (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon) :=
      trace_eq_finrankOneRingEquiv_symm K L hfin _
    _ = (finrankOneRingEquiv K L hfin).symm epsilon *
          (beta * ((frobeniusEquiv K 2) ^ r) beta) := by
      rw [hanchor]
      rw [map_mul, map_mul, map_pow,
        fieldEquiv.symm_apply_apply, hfrobeniusK]
      dsimp only [fieldEquiv]
      ac_rfl

/-- Frobenius-renormalizing a kernel coordinate can instead be undone on the
quotient coordinate, leaving the prescribed kernel coordinate fixed. -/
theorem exists_typeANormalForm_preserving_kernel_coordinate
    {H : Type uP} [Group H]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (hSq : LowerCentralSquaresLieInSecond H)
    (eZero : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
    (eKernel : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] F)
    (sigma : F ≃ₐ[ZMod 2] F)
    (theta : RingAut F)
    (hcomm : ∀ x : F, sigma (theta x) = theta (sigma x))
    (epsilon : F)
    (hformula : ∀ alpha : F,
      (eKernel.trans sigma.toLinearEquiv)
          (lowerCentralSquareMapAdditive H hSq (eZero.symm alpha)) =
        epsilon * (alpha * theta alpha)) :
    ∃ eZero' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F,
      ∃ epsilon' : F,
        ∀ beta : F,
          eKernel
              (lowerCentralSquareMapAdditive H hSq (eZero'.symm beta)) =
            epsilon' * (beta * theta beta) := by
  let eZero' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F :=
    eZero.trans sigma.toLinearEquiv.symm
  refine ⟨eZero', sigma.symm epsilon, ?_⟩
  intro beta
  have h := congrArg sigma.symm (hformula (sigma beta))
  have htheta : sigma.symm (theta (sigma beta)) = theta beta := by
    rw [← hcomm beta, sigma.symm_apply_apply]
  have h' : eKernel
        (lowerCentralSquareMapAdditive H hSq (eZero.symm (sigma beta))) =
      sigma.symm epsilon * (beta * theta beta) := by
    simpa only [LinearEquiv.trans_apply, LinearEquiv.coe_coe,
      AlgEquiv.toLinearEquiv_apply, map_mul, htheta,
      sigma.symm_apply_apply] using h
  have heZero : eZero'.symm beta = eZero.symm (sigma beta) := by
    apply eZero'.injective
    simp only [eZero', LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
    exact (sigma.symm_apply_apply beta).symm
  rw [heZero]
  exact h'

/-- Actor equivariance forces the kernel eigenvalue to be the type-A norm of
the quotient eigenvalue once the kernel coordinate is prescribed. -/
theorem kernel_eigenvalue_eq_typeANorm_of_normalForm
    {H : Type uP} [Group H]
    {C : Type uC} [Group C]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (phi : C →* MulAut H) (c : C)
    (hSq : LowerCentralSquaresLieInSecond H)
    (eZero : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
    (eKernel : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] F)
    (lambda nu : F) (theta : RingAut F)
    (epsilon : F) (hepsilon : epsilon ≠ 0)
    (hcompatZero : ∀ v,
      eZero (lowerCentralLayerRepresentation phi 0 c v) =
        lambda * eZero v)
    (hcompatKernel : ∀ v,
      eKernel (lowerCentralLayerRepresentation phi 1 c v) =
        nu * eKernel v)
    (hnormal : ∀ alpha : F,
      eKernel
          (lowerCentralSquareMapAdditive H hSq (eZero.symm alpha)) =
        epsilon * (alpha * theta alpha)) :
    nu = lambda * theta lambda := by
  let v : Additive (lowerCentralLayer H 0) := eZero.symm 1
  have hv : lowerCentralLayerRepresentation phi 0 c v =
      eZero.symm lambda := by
    apply eZero.injective
    simp only [hcompatZero, v, LinearEquiv.apply_symm_apply, mul_one]
  have hequiv :=
    lowerCentralSquareMapAdditive_equivariant phi hSq c v
  have hcoords := congrArg eKernel hequiv
  rw [hv, hnormal lambda, hcompatKernel, hnormal 1] at hcoords
  simp only [map_one, mul_one] at hcoords
  apply Eq.symm
  apply mul_left_cancel₀ hepsilon
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hcoords

/-! ## The actual square normal form gives type A -/

/-- **Higman Lemma 11 (p. 89), lower-central extension endgame.**

An actual xi-length-two lower-central square normal form supplies all data of
a Peterfalvi type-A Suzuki `2`-group.  The theorem constructs both short
exact-sequence coordinates from the lower-central quotients; it does not posit
an abstract extension or a multiplication law. -/
noncomputable def typeADataOfLowerCentralSquareNormalForm
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (parameter : ℕ)
    (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (phi : RingAut F)
    (phi_ne_one : phi ≠ 1)
    (phi_orderOf_odd : Odd (orderOf phi))
    (epsilon : F)
    (hepsilon : epsilon ≠ 0)
    (eZero : Additive (lowerCentralLayer P 0) ≃+ F)
    (eOne : Additive (lowerCentralLayer P 1) ≃+ F)
    (hnormal : ∀ alpha : F,
      eOne (lowerCentralSquareMapAdditive P
        (lowerCentralSquaresLieInSecond_of_agemo_eq P
          (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen))
        (eZero.symm alpha)) =
          epsilon * (alpha * phi alpha)) :
    TypeAData P := by
  let hSq : LowerCentralSquaresLieInSecond P :=
    lowerCentralSquaresLieInSecond_of_agemo_eq P
      (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)
  have hK0 : lowerCentralLayerKernel P 0 =
      (lowerCentralTerm P 1).subgroupOf (lowerCentralTerm P 0) :=
    lowerCentralLayerKernel_zero_eq_of_squares_le P hSq
  have hAmbientK1 : lowerCentralLayerKernelInAmbient P 1 = ⊥ := by
    rw [lowerCentralLayerKernelInAmbient_eq,
      show 1 + 1 = 2 by omega,
      lowerCentralTerm_two_eq_bot hP hncomm hxi hlen, sup_bot_eq,
      lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      frattini_agemo_one_map_eq_bot hP hncomm hxi hlen]
  have hK1 : lowerCentralLayerKernel P 1 = ⊥ := by
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 1, hAmbientK1]
    simp
  let left : Multiplicative F ≃* lowerCentralTerm P 1 :=
    lowerCentralExtensionLeft hK1 eOne
  let right : P ⧸ lowerCentralTerm P 1 ≃* Multiplicative F :=
    lowerCentralExtensionRight hK0 eZero
  have hcentral : lowerCentralTerm P 1 ≤ Subgroup.center P := by
    rw [lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      (commutator_eq_frattini_and_frattini_eq_center
        hP hncomm hxi hlen).2]
  have hsquareCoordinates : ∀ x : P, x ^ 2 =
      left (Multiplicative.ofAdd
        (epsilon *
          ((right (QuotientGroup.mk' (lowerCentralTerm P 1) x)).toAdd *
            phi (right
              (QuotientGroup.mk' (lowerCentralTerm P 1) x)).toAdd))) := by
    intro x
    let xZero : lowerCentralTerm P 0 :=
      ⟨x, by simp [lowerCentralTerm]⟩
    let alpha : F := eZero (Additive.ofMul
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0) xZero))
    have hright :
        (right (QuotientGroup.mk' (lowerCentralTerm P 1) x)).toAdd =
          alpha := by
      rfl
    have hnormal' :
        eOne (lowerCentralSquareMapAdditive P hSq
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0) xZero))) =
          epsilon * (alpha * phi alpha) := by
      simpa only [hSq, alpha, eZero.symm_apply_apply] using hnormal alpha
    calc
      x ^ 2 = left (Multiplicative.ofAdd
          (eOne (lowerCentralSquareMapAdditive P hSq
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
                xZero))))) :=
        lowerCentralExtensionLeft_square hSq hK1 eOne xZero
      _ = left (Multiplicative.ofAdd
          (epsilon * (alpha * phi alpha))) := by rw [hnormal']
      _ = left (Multiplicative.ofAdd
          (epsilon *
            ((right
              (QuotientGroup.mk' (lowerCentralTerm P 1) x)).toAdd *
              phi (right
                (QuotientGroup.mk' (lowerCentralTerm P 1) x)).toAdd))) := by
        rw [hright]
  exact typeADataOfScaledSquareCoordinates (P := P) (F := F)
    parameter parameter_pos card_field phi phi_ne_one phi_orderOf_odd
    (lowerCentralTerm P 1) left right hcentral epsilon hepsilon
    hsquareCoordinates

/-! ## Higman's source-facing type-A conclusion -/

set_option maxHeartbeats 800000 in
-- This assembly elaborates the two large actual Singer-basis expressions.
/-- Assemble the coordinate content of Higman's Lemma 11 from the two actual
finite-field eigenmodels.  The returned algebra automorphism records every
second-layer Frobenius normalization, so the caller's prescribed kernel
coordinate is retained as `eTwo.trans sigma.toLinearEquiv`. -/
theorem exists_higmanLemmaElevenFieldCoordinates_with_trackedKernel
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    {K : Type uK} {L : Type uL}
    [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [CharP L 2] [Algebra (ZMod 2) L]
    (m n d : Nat)
    (hfinL : finrank (ZMod 2) L = m)
    (hfinK : finrank (ZMod 2) K = n)
    (hfinLayerTwo : finrank (ZMod 2)
      (Additive (lowerCentralLayer P 1)) = n)
    (hnTwo : 2 ≤ n)
    (hdegree : m = d * n)
    (hdegreeOdd : Odd d)
    (iota : K →ₐ[ZMod 2] L)
    (eOne : Additive (lowerCentralLayer P 0) ≃ₗ[ZMod 2] L)
    (eTwo : Additive (lowerCentralLayer P 1) ≃ₗ[ZMod 2] K)
    (c : Y) (hcgen : ∀ y : Y, y ∈ Subgroup.zpowers c)
    (lambda : L) (nu : K)
    (hlambdaGen : Algebra.adjoin (ZMod 2) ({lambda} : Set L) = ⊤)
    (hcompatOne : ∀ v,
      eOne (lowerCentralLayerRepresentation Y.subtype 0 c v) =
        lambda * eOne v)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hcompatTwo : ∀ v,
      eTwo (lowerCentralLayerRepresentation Y.subtype 1 c v) =
        nu * eTwo v)
    (hactorOdd : Odd (Nat.card Y)) :
    ∃ (r : Fin (finrank (ZMod 2) K))
      (eQuot : Additive (lowerCentralLayer P 0) ≃ₗ[ZMod 2] K)
      (lambdaK : K) (sigma : K ≃ₐ[ZMod 2] K) (epsilonK : K),
      epsilonK ≠ 0 ∧
      (∀ v,
        eQuot (lowerCentralLayerRepresentation Y.subtype 0 c v) =
          lambdaK * eQuot v) ∧
      let theta : RingAut K := (frobeniusEquiv K 2) ^ r.val
      theta ≠ 1 ∧
      Odd (orderOf theta) ∧
      (∀ x : K, sigma (theta x) = theta (sigma x)) ∧
      ∀ beta : K,
        (eTwo.trans sigma.toLinearEquiv)
            (lowerCentralSquareMapAdditive P
              (lowerCentralSquaresLieInSecond_of_agemo_eq P
                (agemo_one_eq_lowerCentralTerm_one
                  hP hncomm hxi hlen))
              (eQuot.symm beta)) =
          epsilonK * (beta * theta beta) := by
  classical
  have hnpos : 0 < n := by omega
  have hdpos : 0 < d := hdegreeOdd.pos
  have hmpos : 0 < m := by
    rw [hdegree]
    exact Nat.mul_pos hdpos hnpos
  letI : IsCyclic Y := hxi.cyclic
  letI : CommGroup Y := IsCyclic.commGroup
  letI : NeZero n := ⟨hnpos.ne'⟩
  letI : NeZero m := ⟨hmpos.ne'⟩
  letI : NeZero (finrank (ZMod 2) K) := ⟨by
    rw [hfinK]
    exact hnpos.ne'⟩
  letI : NeZero (finrank (ZMod 2) L) := ⟨by
    rw [hfinL]
    exact hmpos.ne'⟩
  letI : Algebra K L := iota.toRingHom.toAlgebra
  have hiota : ∀ z : K, iota z = algebraMap K L z := by
    intro z
    rfl
  have hfinKL : finrank K L = d := by
    apply Nat.eq_of_mul_eq_mul_left hnpos
    calc
      n * finrank K L =
          finrank (ZMod 2) K * finrank K L := by rw [hfinK]
      _ = finrank (ZMod 2) L :=
        Module.finrank_mul_finrank (ZMod 2) K L
      _ = m := hfinL
      _ = d * n := hdegree
      _ = n * d := Nat.mul_comm _ _
  have hcardK :
      Nat.card K = 2 ^ finrank (ZMod 2) K := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank
        (K := ZMod 2) (V := K))
  have hcardL :
      Nat.card L = 2 ^ finrank (ZMod 2) L := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank
        (K := ZMod 2) (V := L))
  have hirrOne : Representation.IsIrreducible
      (lowerCentralLayerRepresentation Y.subtype 0) :=
    lowerCentralLayerZeroRepresentation_isIrreducible_of_xiLengthTwo
      hP hncomm hxi hlen
  have hfaithOne : Function.Injective
      (lowerCentralLayerRepresentation Y.subtype 0) :=
    lowerCentralLayerZeroRepresentation_injective_of_odd_faithful_action
      hP Y.subtype Y.subtype_injective hactorOdd
  have htransTwo : ∀ v w : Additive (lowerCentralLayer P 1),
      v ≠ 0 → w ≠ 0 →
        ∃ y : Y,
          lowerCentralLayerRepresentation Y.subtype 1 y v = w :=
    lowerCentralLayerOneRepresentation_transitive_of_xiLengthTwo
      hP hncomm hxi hlen
  have hnK : 0 < finrank (ZMod 2) K := by
    rw [hfinK]
    exact hnpos
  have hnKTwo : 2 ≤ finrank (ZMod 2) K := by
    rw [hfinK]
    exact hnTwo
  have hprimNuK :
      IsPrimitiveRoot nu (2 ^ finrank (ZMod 2) K - 1) := by
    simpa only [hfinK] using hnuPrimitive
  obtain ⟨s, eOne', eTwo', lambda', nu', r, heTwo',
      hcompatOne', hlambdaGen', hcompatTwo', hnuPrimitive',
      hnu, hr, hbracket, _hcoordinate, hpairGap⟩ :=
    exists_normalizedLowerCentralConjugateBasisBracketCoordinate_with_secondShift
      Y.subtype c eOne lambda hlambdaGen hcompatOne
      eTwo nu iota hcompatTwo hnKTwo hprimNuK
  let bTwo :=
    conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo'
  obtain ⟨epsilon, hepsilon, hseedDirect⟩ :=
    exists_ne_zero_smul_secondConjugateBasis_zero_of_bracket
      Y.subtype c eOne' lambda' hcompatOne'
      eTwo' nu' iota hcompatTwo' hnKTwo hnuPrimitive'
      r hnu hbracket
  have hdegreeTrace :
      finrank (ZMod 2) L = finrank (ZMod 2) K * d := by
    calc
      finrank (ZMod 2) L = m := hfinL
      _ = d * n := hdegree
      _ = n * d := Nat.mul_comm _ _
      _ = finrank (ZMod 2) K * d := by rw [hfinK]
  have hrtwo : r + r ≠ 0 :=
    twice_gap_ne_zero_of_odd_degree
      (L := L) (m := finrank (ZMod 2) L)
      (n := finrank (ZMod 2) K) (d := d)
      rfl hnK hdegreeTrace hdegreeOdd
      lambda' (iota nu')
      (hnuPrimitive'.map_of_injective iota.injective)
      r hr hnu
  let N := finrank (ZMod 2) L
  let bOne := canonicalFirstBasisReindexed eOne' N rfl
  have hbOne :
      bOne = conjugateTensorBasisOfLinearEquiv L eOne' := by
    simp [bOne, N, canonicalFirstBasisReindexed]
  have hseed :
      lowerCentralCommutatorBilinearBaseChange L P
          (bOne 0) (bOne (0 + r)) =
        epsilon • bTwo 0 := by
    simpa only [hbOne, bTwo, zero_add] using hseedDirect
  have hpairGap' : ∀ i j : Fin N,
      lowerCentralCommutatorBilinearBaseChange L P
          (bOne i) (bOne j) ≠ 0 →
        HasHigmanPairGap (ZMod.finEquiv N r) i j := by
    simpa only [N, hbOne] using hpairGap
  have hsupport : ∀ i j : Fin N,
      j ≠ i + r → i ≠ j + r →
        lowerCentralCommutatorBilinearBaseChange L P
          (bOne i) (bOne j) = 0 := by
    intro i j hj hi
    exact eq_zero_of_pairGapSupport r
      (fun a b : Fin N =>
        lowerCentralCommutatorBilinearBaseChange L P
          (bOne a) (bOne b))
      hpairGap' i j hj hi
  have hsymm : ∀ i j : Fin N,
      lowerCentralCommutatorBilinearBaseChange L P
          (bOne i) (bOne j) =
        lowerCentralCommutatorBilinearBaseChange L P
          (bOne j) (bOne i) := by
    intro i j
    unfold lowerCentralCommutatorBilinearBaseChange
    exact LinearMap.BilinMap.baseChange_isSymm
      (LinearMap.BilinMap.zmodTwo_symmetric_of_self_eq_zero
        (lowerCentralCommutatorBilinear P)
        (lowerCentralCommutatorBilinear_self P))
      (bOne i) (bOne j)
  let hSq := lowerCentralSquaresLieInSecond_of_agemo_eq P
    (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)
  have hq : ∀ x : Additive (lowerCentralLayer P 0),
      lowerCentralSquareMapBaseChange L P hSq x =
        ∑ i : Fin N, ∑ j : Fin N with i < j,
          (eOne' x) ^ (2 ^ i.val + 2 ^ j.val) •
            lowerCentralCommutatorBilinearBaseChange L P
              (bOne i) (bOne j) := by
    exact lowerCentralSquareMapBaseChange_eq_frobeniusSum_of_generator
      Y.subtype hSq n hnTwo hfinLayerTwo
      hirrOne hfaithOne htransTwo
      eOne' N rfl c hcgen lambda' hcompatOne'
  have hcycleOne : ∀ i : Fin N,
      frobeniusScalarBaseChange L (bOne i) =
        bOne (higmanCyclicSucc
          ((show finrank (ZMod 2) L = N from rfl) ▸ finrank_pos) i) := by
    exact frobeniusScalarBaseChange_canonicalFirstBasisReindexed
      eOne' N rfl
  have hcycleTwo : ∀ s : Fin (finrank (ZMod 2) K),
      frobeniusScalarBaseChange L (bTwo s) =
        bTwo (higmanCyclicSucc hnK s) := by
    exact frobeniusScalarBaseChange_canonicalSecondBasis iota eTwo'
  have hNdegree : N = d * finrank (ZMod 2) K := by
    calc
      N = m := hfinL
      _ = d * n := hdegree
      _ = d * finrank (ZMod 2) K := by rw [hfinK]
  obtain ⟨eTwoShift, heTwoShift, htrace⟩ :=
    exists_lowerCentralSquareMap_eq_anchoredTrace_of_actualSingerData_indexed_with_secondShift
      (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)
      iota hiota N d hNdegree hnK hdpos hcardK hfinKL rfl
      eOne' bOne hq hcycleOne
      eTwo' bTwo rfl hcycleTwo
      0 0 r hr hrtwo epsilon hseed hsymm hsupport
  have hoddKL : Odd (finrank K L) := by
    rw [hfinKL]
    exact hdegreeOdd
  have hfinOne : finrank K L = 1 :=
    finrank_eq_one_of_anchoredTrace_lowerCentralSquareMap_of_xiLengthTwo
      hP hncomm hxi hlen
      eOne'.toAddEquiv
      eTwoShift.symm.toLinearMap.toAddMonoidHom
      hoddKL 0 r.val epsilon htrace
  have hdOne : d = 1 := hfinKL.symm.trans hfinOne
  have hmn : m = n := by
    calc
      m = d * n := hdegree
      _ = 1 * n := by rw [hdOne]
      _ = n := one_mul n
  have hfieldDegrees :
      finrank (ZMod 2) L = finrank (ZMod 2) K := by
    calc
      finrank (ZMod 2) L = m := hfinL
      _ = n := hmn
      _ = finrank (ZMod 2) K := hfinK.symm
  have hshiftPrimitive :
      IsPrimitiveRoot
        (lambda' ^ (1 + 2 ^ r.val))
        (2 ^ finrank (ZMod 2) L - 1) := by
    rw [← hnu]
    change IsPrimitiveRoot (iota.toRingHom nu')
      (2 ^ finrank (ZMod 2) L - 1)
    simpa only [hfieldDegrees] using
      (hnuPrimitive'.map_of_injective iota.injective)
  let fieldEquiv : K ≃+* L := finrankOneRingEquiv K L hfinOne
  let rK : Fin (finrank (ZMod 2) K) :=
    ⟨r.val, by
      rw [← hfieldDegrees]
      exact r.isLt⟩
  have hrK : rK ≠ 0 := by
    intro hrKZero
    apply hr
    apply Fin.ext
    simpa [rK] using congrArg Fin.val hrKZero
  obtain ⟨eQuotAdd, lambdaK, epsilonK, _, hlambdaK, hepsilonK,
      hcompatQuotAdd, hnormalAdd⟩ :=
    exists_lowerCentralQuotientCoordinate_typeANormalForm_of_anchoredTrace_finrankOne_generator
      Y.subtype c hfinOne hSq eOne' lambda' hcompatOne'
      eTwoShift 0 r.val epsilon htrace
  have hlambdaK' : lambdaK = fieldEquiv.symm lambda' := by
    simpa using hlambdaK
  have hshiftPrimitiveK :
      IsPrimitiveRoot
        (lambdaK ^ (1 + 2 ^ rK.val))
        (2 ^ finrank (ZMod 2) K - 1) := by
    have hmapped :=
      hshiftPrimitive.map_of_injective fieldEquiv.symm.injective
    rw [hlambdaK']
    simpa only [fieldEquiv, pow_zero, one_apply, map_pow,
      hfieldDegrees, rK]
      using hmapped
  obtain ⟨hphiNeK, hphiOddK⟩ :=
    frobeniusPower_ne_one_and_orderOf_odd_of_primitive_shift
      hcardK lambdaK rK hrK hshiftPrimitiveK
  let eQuot : Additive (lowerCentralLayer P 0) ≃ₗ[ZMod 2] K :=
    eQuotAdd.toLinearEquiv
      (fun z x => ZMod.map_smul eQuotAdd.toAddMonoidHom z x)
  have hepsilonKNe : epsilonK ≠ 0 := by
    intro hzero
    apply hepsilon
    apply fieldEquiv.symm.injective
    rw [← hepsilonK]
    simpa only [map_zero] using hzero
  have hcompatQuot : ∀ v,
      eQuot (lowerCentralLayerRepresentation Y.subtype 0 c v) =
        lambdaK * eQuot v := by
    intro v
    change eQuotAdd
        (lowerCentralLayerRepresentation Y.subtype 0 c v) =
      lambdaK * eQuotAdd v
    exact hcompatQuotAdd v
  have hnormal : ∀ beta : K,
      eTwoShift
          (lowerCentralSquareMapAdditive P hSq (eQuot.symm beta)) =
        epsilonK *
          (beta * ((frobeniusEquiv K 2) ^ rK.val) beta) := by
    intro beta
    change eTwoShift
        (lowerCentralSquareMapAdditive P hSq
          (eQuotAdd.symm beta)) = _
    simpa only [rK] using hnormalAdd beta
  let sigma : K ≃ₐ[ZMod 2] K :=
    ((FiniteField.frobeniusAlgEquivOfAlgebraic
      (ZMod 2) K) ^ s.val).trans
      ((FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) K) ^ (0 : Nat))
  have hTwoCombined :
      eTwoShift = eTwo.trans sigma.toLinearEquiv := by
    rw [heTwoShift, heTwo']
    rfl
  have hsigmaTheta : ∀ x : K,
      sigma (((frobeniusEquiv K 2) ^ rK.val) x) =
        ((frobeniusEquiv K 2) ^ rK.val) (sigma x) := by
    intro x
    rw [← iterateFrobeniusEquiv_eq_pow]
    simp only [iterateFrobeniusEquiv_def, map_pow]
  have hnormalCombined : ∀ beta : K,
      (eTwo.trans sigma.toLinearEquiv)
          (lowerCentralSquareMapAdditive P hSq (eQuot.symm beta)) =
        epsilonK *
          (beta * ((frobeniusEquiv K 2) ^ rK.val) beta) := by
    intro beta
    rw [← hTwoCombined]
    exact hnormal beta
  refine ⟨rK, eQuot, lambdaK, sigma, epsilonK,
    hepsilonKNe, hcompatQuot, ?_⟩
  dsimp only
  exact ⟨hphiNeK, hphiOddK, hsigmaTheta, hnormalCombined⟩

set_option maxHeartbeats 800000 in
-- The compatibility projection re-elaborates the tracked field assembly.
/-- Compatibility projection of the tracked field-coordinate assembly to the
original nonempty type-A data endpoint. -/
private theorem typeAData_of_higmanLemmaElevenFieldData
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    {K L : Type uF}
    [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [CharP L 2] [Algebra (ZMod 2) L]
    (m n d : Nat)
    (hfinL : finrank (ZMod 2) L = m)
    (hfinK : finrank (ZMod 2) K = n)
    (hfinLayerTwo : finrank (ZMod 2)
      (Additive (lowerCentralLayer P 1)) = n)
    (hnTwo : 2 ≤ n)
    (hdegree : m = d * n)
    (hdegreeOdd : Odd d)
    (iota : K →ₐ[ZMod 2] L)
    (eOne : Additive (lowerCentralLayer P 0) ≃ₗ[ZMod 2] L)
    (eTwo : Additive (lowerCentralLayer P 1) ≃ₗ[ZMod 2] K)
    (c : Y) (hcgen : ∀ y : Y, y ∈ Subgroup.zpowers c)
    (lambda : L) (nu : K)
    (hlambdaGen : Algebra.adjoin (ZMod 2) ({lambda} : Set L) = ⊤)
    (hcompatOne : ∀ v,
      eOne (lowerCentralLayerRepresentation Y.subtype 0 c v) =
        lambda * eOne v)
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1))
    (hcompatTwo : ∀ v,
      eTwo (lowerCentralLayerRepresentation Y.subtype 1 c v) =
        nu * eTwo v)
    (hactorOdd : Odd (Nat.card Y)) :
    Nonempty (TypeAData.{uP, uF} P) := by
  classical
  obtain ⟨r, eQuot, _, sigma, epsilonK,
      hepsilonK, _, hphiNe, hphiOdd, _, hnormal⟩ :=
    exists_higmanLemmaElevenFieldCoordinates_with_trackedKernel
      hP hncomm hxi hlen m n d hfinL hfinK hfinLayerTwo hnTwo
      hdegree hdegreeOdd iota eOne eTwo c hcgen lambda nu
      hlambdaGen hcompatOne hnuPrimitive hcompatTwo hactorOdd
  have hcardK : Nat.card K = 2 ^ finrank (ZMod 2) K := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K))
  exact ⟨typeADataOfLowerCentralSquareNormalForm.{uP, uF}
    (P := P) (Y := Y) (F := K)
    hP hncomm hxi hlen
    (finrank (ZMod 2) K) finrank_pos hcardK
    ((frobeniusEquiv K 2) ^ r.val) hphiNe hphiOdd
    epsilonK hepsilonK eQuot.toAddEquiv
      (eTwo.trans sigma.toLinearEquiv).toAddEquiv hnormal⟩

set_option maxHeartbeats 800000 in
-- The source endpoint elaborates the complete field-model assembly above.
/-- **Higman Lemma 11 (pp. 88--89).**

For the original cyclic actor, Higman's prime-support hypothesis and the
existence of more than one involution force every noncommutative
xi-length-two group to be of type A. -/
theorem higmanLemmaEleven
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    IsTypeA.{uP, 0} P := by
  classical
  letI : IsCyclic Y := hxi.cyclic
  letI : CommGroup Y := IsCyclic.commGroup
  let m := finrank (ZMod 2)
    (Additive (lowerCentralLayer P 0))
  let n := finrank (ZMod 2)
    (Additive (lowerCentralLayer P 1))
  letI : Nontrivial (lowerCentralLayer P 0) :=
    lowerCentralLayer_zero_nontrivial_of_xiLengthTwo
      hP hncomm hxi hlen
  letI : Nontrivial (Additive (lowerCentralLayer P 0)) := inferInstance
  letI : Nontrivial (lowerCentralLayer P 1) :=
    lowerCentralLayer_one_nontrivial_of_not_isMulCommutative hP hncomm
  letI : Nontrivial (Additive (lowerCentralLayer P 1)) := inferInstance
  have hmpos : 0 < m := by
    dsimp [m]
    exact finrank_pos
  have hnpos : 0 < n := by
    dsimp [n]
    exact finrank_pos
  have hactorOdd : Odd (Nat.card Y) :=
    actor_card_odd_of_primeSupport_xiLengthTwo
      hP hncomm hxi hlen hprime
  obtain ⟨c, eOne, mu, hcgen, _hmu, hcompatOneAll,
      _hlambdaOrder, hlambdaGen, hnm, hquotientOdd⟩ :=
    exists_originalXiActor_degree_dvd_and_odd_quotient
      hP hncomm hxi hlen hprime
  let lambda : GaloisField 2 m := (mu c : GaloisField 2 m)
  have hcompatOne : ∀ v,
      eOne (lowerCentralLayerRepresentation Y.subtype 0 c v) =
        lambda * eOne v := hcompatOneAll c
  let d := m / n
  have hdegree : m = d * n := by
    exact (Nat.div_mul_cancel hnm).symm
  have hdegreeOdd : Odd d := by
    simpa only [d] using hquotientOdd
  obtain ⟨x, y, hx, hy, hxy⟩ := hmulti
  have hinvTwo : 2 ≤ (involutions P).ncard := by
    calc
      2 = ({x, y} : Set P).ncard := (Set.ncard_pair hxy).symm
      _ ≤ (involutions P).ncard := by
        apply Set.ncard_mono
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
  have hinvCard : (involutions P).ncard = 2 ^ n - 1 := by
    simpa only [n] using
      involutions_ncard_eq_pow_finrank_lowerCentralLayer_one_sub_one
        hP hncomm hxi hlen
  have hnTwo : 2 ≤ n := by
    by_contra h
    have hnOne : n = 1 := by omega
    rw [hinvCard, hnOne] at hinvTwo
    norm_num at hinvTwo
  obtain ⟨iota⟩ : Nonempty
      (GaloisField 2 n →ₐ[ZMod 2] GaloisField 2 m) := by
    apply FiniteField.nonempty_algHom_of_finrank_dvd
    rw [GaloisField.finrank 2 hnpos.ne',
      GaloisField.finrank 2 hmpos.ne']
    exact hnm
  have htransTwo : ∀ v w : Additive (lowerCentralLayer P 1),
      v ≠ 0 → w ≠ 0 →
        ∃ y : Y,
          lowerCentralLayerRepresentation Y.subtype 1 y v = w :=
    lowerCentralLayerOneRepresentation_transitive_of_xiLengthTwo
      hP hncomm hxi hlen
  obtain ⟨eTwo, nu, _bTwo, hnuPrimitive, hconjTwo,
      _hnuGen, _hbTwo⟩ :=
    exists_singerFrobeniusEigenbasis_of_transitive_generator
      (lowerCentralLayerRepresentation Y.subtype 1)
      n hnTwo rfl htransTwo c hcgen
  have hcompatTwo : ∀ v,
      eTwo (lowerCentralLayerRepresentation Y.subtype 1 c v) =
        nu * eTwo v := by
    intro v
    have hv := DFunLike.congr_fun hconjTwo (eTwo v)
    simpa using hv
  exact typeAData_of_higmanLemmaElevenFieldData
    (K := GaloisField 2 n) (L := GaloisField 2 m)
    hP hncomm hxi hlen
    m n d
    (GaloisField.finrank 2 hmpos.ne')
    (GaloisField.finrank 2 hnpos.ne')
    rfl hnTwo hdegree hdegreeOdd
    iota eOne eTwo c hcgen lambda nu
    hlambdaGen hcompatOne hnuPrimitive hcompatTwo hactorOdd

end

end OddOrder.Higman.Suzuki2Groups
