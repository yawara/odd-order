/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralSpectrum

/-!
# Higman's classification of Suzuki 2-groups of length two

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 11, pp. 88--89.

The proof keeps the two finite-field degrees separate until Higman's trace
argument rules out a proper odd extension.  This leaf contains the common
splitting-field eigenbasis and unequal-degree bracket normal form.  The trace
calculation is collected in the downstream `TraceFormula` leaf.
-/

set_option autoImplicit false

open Module Polynomial
open OddOrder.RepresentationTheory
open scoped TensorProduct BigOperators Fin.NatCast IsMulCommutative

namespace OddOrder.Higman.Suzuki2Groups

universe uCommonField uK uL uGroup

/-! ## The second-layer Singer basis in a common splitting field -/

/-- Singer--Frobenius coordinates transported to a chosen finite splitting
field containing the canonical Singer field.  Faithfulness of the original
action is not assumed: it is recovered on the effective image. -/
theorem exists_singerFrobeniusEigenbasis_of_transitive_generator_over
    {C V L : Type uCommonField} [CommGroup C] [IsCyclic C] [Finite C]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    (rho : Representation (ZMod 2) C V) (n : ℕ) (hn : 2 ≤ n)
    (hfin : Module.finrank (ZMod 2) V = n)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ c : C, rho c v = w)
    (c : C) (hcgen : ∀ x : C, x ∈ Subgroup.zpowers c)
    (iota : GaloisField 2 n →ₐ[ZMod 2] L) :
    ∃ (e : V ≃ₗ[ZMod 2] GaloisField 2 n) (nu : GaloisField 2 n)
      (b : Basis (Fin n) L (L ⊗[ZMod 2] V)),
      IsPrimitiveRoot nu (2 ^ n - 1) ∧
      e.conj (rho c) = Algebra.lmul (ZMod 2) (GaloisField 2 n) nu ∧
      Algebra.adjoin (ZMod 2) ({nu} : Set (GaloisField 2 n)) = ⊤ ∧
      IsPrimitiveRoot (iota nu) (2 ^ n - 1) ∧
      ∀ s, (rho c).baseChange L (b s) =
        (iota nu) ^ (2 ^ s.val) • b s := by
  obtain ⟨e, nu, _bK, hprim, hconj, hgen, _hbK⟩ :=
    exists_singerFrobeniusEigenbasis_of_transitive_generator
      rho n hn hfin htrans c hcgen
  have hcharK : (rho c).charpoly = minpoly (ZMod 2) nu :=
    charpoly_eq_minpoly_of_conj_lmul (rho c) e nu hconj hgen
  have hcharL : (rho c).charpoly = minpoly (ZMod 2) (iota nu) := by
    calc
      (rho c).charpoly = minpoly (ZMod 2) nu := hcharK
      _ = minpoly (ZMod 2) (iota nu) :=
        (minpoly.algHom_eq iota iota.injective nu).symm
  have hprimL : IsPrimitiveRoot (iota nu) (2 ^ n - 1) :=
    hprim.map_of_injective iota.injective
  obtain ⟨b, hb⟩ := exists_frobeniusEigenbasis_of_charpoly_eq_minpoly
    (rho c) n hn (iota nu) hfin hcharL hprimL
  exact ⟨e, nu, b, hprim, hconj, hgen, hprimL, hb⟩

/-- The transitive Singer model, transported to the canonical normalized
Frobenius-conjugate basis in a chosen common splitting field. -/
theorem exists_singerConjugateBasis_of_transitive_generator_over
    {C V L : Type uCommonField} [CommGroup C] [IsCyclic C] [Finite C]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    (rho : Representation (ZMod 2) C V) (n : ℕ) (hn : 2 ≤ n)
    (hfin : finrank (ZMod 2) V = n)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ c : C, rho c v = w)
    (c : C) (hcgen : ∀ x : C, x ∈ Subgroup.zpowers c)
    (iota : GaloisField 2 n →ₐ[ZMod 2] L) :
    ∃ (e : V ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n)
      (b : Basis (Fin (finrank (ZMod 2) (GaloisField 2 n))) L
        (L ⊗[ZMod 2] V)),
      IsPrimitiveRoot nu (2 ^ n - 1) ∧
      e.conj (rho c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu ∧
      Algebra.adjoin (ZMod 2)
        ({nu} : Set (GaloisField 2 n)) = ⊤ ∧
      IsPrimitiveRoot (iota nu) (2 ^ n - 1) ∧
      b = conjugateTensorBasisAlongOfLinearEquiv
        (GaloisField 2 n) L iota e ∧
      (∀ v : V,
        (1 : L) ⊗ₜ[ZMod 2] v =
          ∑ i : Fin (finrank (ZMod 2) (GaloisField 2 n)),
            iota ((e v) ^ (2 ^ i.val)) • b i) ∧
      (∀ i,
        (rho c).baseChange L (b i) =
          iota (nu ^ (2 ^ i.val)) • b i) ∧
      ∀ i,
        frobeniusScalarBaseChange L (b i) =
          b (frobeniusCoordinateSucc (GaloisField 2 n) i) := by
  obtain ⟨e, nu, _b, hprim, hconj, hgen, _hb⟩ :=
    exists_singerFrobeniusEigenbasis_of_transitive_generator
      rho n hn hfin htrans c hcgen
  let b := conjugateTensorBasisAlongOfLinearEquiv
    (GaloisField 2 n) L iota e
  have hcompat : ∀ v : V, e (rho c v) = nu * e v := by
    intro v
    have hv := DFunLike.congr_fun hconj (e v)
    simpa using hv
  refine ⟨e, nu, b, hprim, hconj, hgen,
    hprim.map_of_injective iota.injective, rfl, ?_, ?_, ?_⟩
  · intro v
    exact one_tmul_eq_sum_conjugateTensorBasisAlongOfLinearEquiv
      (GaloisField 2 n) L iota e v
  · intro i
    exact baseChange_eigen_conjugateTensorBasisAlongOfLinearEquiv
      (GaloisField 2 n) L iota e (rho c) nu hcompat i
  · intro i
    exact frobeniusScalarBaseChange_conjugateTensorBasisAlongOfLinearEquiv
      (GaloisField 2 n) L iota e i

/-! ## Unequal-degree pair-gap arithmetic -/

private def residueFin {n : ℕ} (hn : 0 < n) (a : ℕ) : Fin n :=
  ⟨a % n, Nat.mod_lt _ hn⟩

private theorem twoPower_modEq_mersenne_remainder
    {n a : ℕ} (hn : 0 < n) :
    Nat.ModEq (2 ^ n - 1) (2 ^ a) (2 ^ (residueFin hn a).val) := by
  have hpowpos : 0 < 2 ^ n := by positivity
  have hbase : Nat.ModEq (2 ^ n - 1) (2 ^ n) 1 := by
    convert Nat.add_modEq_left (n := 2 ^ n - 1) (a := 1) using 1
    all_goals omega
  have ha : a = n * (a / n) + a % n := (Nat.div_add_mod a n).symm
  change Nat.ModEq (2 ^ n - 1) (2 ^ a) (2 ^ (a % n))
  conv_lhs => rw [ha, pow_add, pow_mul]
  simpa using
    (hbase.pow (a / n)).mul (Nat.ModEq.refl (2 ^ (a % n)))

private theorem twoPower_modEq_mersenne_of_index_modEq
    {n a b : ℕ} (hn : 0 < n) (h : Nat.ModEq n a b) :
    Nat.ModEq (2 ^ n - 1) (2 ^ a) (2 ^ b) := by
  have hab : a % n = b % n := h
  calc
    2 ^ a ≡ 2 ^ (a % n) [MOD 2 ^ n - 1] := by
      simpa [residueFin] using
        twoPower_modEq_mersenne_remainder hn (a := a)
    _ = 2 ^ (b % n) := by rw [hab]
    _ ≡ 2 ^ b [MOD 2 ^ n - 1] := by
      simpa [residueFin] using
        (twoPower_modEq_mersenne_remainder hn (a := b)).symm

private theorem twoPower_cyclicAdd_modEq'
    {m : ℕ} [NeZero m] (a s : Fin m) :
    Nat.ModEq (2 ^ m - 1) (2 ^ (a.val + s.val)) (2 ^ (a + s).val) := by
  have hpowpos : 0 < 2 ^ m := by positivity
  have hbase : Nat.ModEq (2 ^ m - 1) (2 ^ m) 1 := by
    convert Nat.add_modEq_left (n := 2 ^ m - 1) (a := 1) using 1
    all_goals omega
  by_cases hwrap : m ≤ a.val + s.val
  · have hval : (a + s).val = a.val + s.val - m := by
      rw [Fin.val_add_eq_ite]
      simp [hwrap]
    have hsum : a.val + s.val = m + (a.val + s.val - m) := by omega
    rw [hsum, pow_add, hval]
    simpa using hbase.mul
      (Nat.ModEq.refl (2 ^ (a.val + s.val - m)))
  · have hval : (a + s).val = a.val + s.val := by
      rw [Fin.val_add_eq_ite]
      simp [hwrap]
    rw [hval]

private theorem primitiveRoot_singleWeight_injective
    {F : Type*} [Field F] {n : ℕ} (hn : 2 ≤ n)
    (zeta : F) (hprim : IsPrimitiveRoot zeta (2 ^ n - 1)) :
    Function.Injective (fun i : Fin n => zeta ^ (2 ^ i.val)) := by
  intro i j hij
  have hi_half : 2 ^ i.val ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hj_half : 2 ^ j.val ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hn_pow : 2 ^ (n - 1) < 2 ^ n - 1 := by
    have hn_half_two : 2 ≤ 2 ^ (n - 1) := by
      calc
        2 = 2 ^ 1 := by simp
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have heq : 2 ^ n = 2 ^ (n - 1) * 2 := by
      calc
        2 ^ n = 2 ^ ((n - 1) + 1) := by
          congr 1
          all_goals omega
        _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
    omega
  apply Fin.ext
  exact (Nat.pow_right_injective (by omega : 1 < 2))
    (hprim.pow_inj (hi_half.trans_lt hn_pow) (hj_half.trans_lt hn_pow) hij)

/-- Equality of primitive pair weights identifies both index pairs up to
order, including the case in which either pair has repeated residues. -/
private theorem primitiveRoot_pairWeight_eq_pairWeight_candidates_all
    {F : Type*} [Field F] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 2 ≤ n)
    (zeta : F) (hprim : IsPrimitiveRoot zeta (2 ^ n - 1))
    (a b c d : Fin n)
    (h : zeta ^ (2 ^ a.val + 2 ^ b.val) =
      zeta ^ (2 ^ c.val + 2 ^ d.val)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hcd : c = d
  · subst d
    by_cases hab : a = b
    · subst b
      have hsquare :
          (zeta ^ (2 ^ a.val)) ^ 2 = (zeta ^ (2 ^ c.val)) ^ 2 := by
        simpa only [← pow_mul,
          show 2 ^ a.val * 2 = 2 ^ a.val + 2 ^ a.val by omega,
          show 2 ^ c.val * 2 = 2 ^ c.val + 2 ^ c.val by omega] using h
      have hsingle : zeta ^ (2 ^ a.val) = zeta ^ (2 ^ c.val) := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hs | hs
        · exact hs
        · have hneg : -(zeta ^ (2 ^ c.val)) = zeta ^ (2 ^ c.val) := by
            have hz : (-1 : ZMod 2) = 1 := by decide
            have hnegOne : (-1 : F) = 1 := by
              calc
                (-1 : F) = algebraMap (ZMod 2) F (-1 : ZMod 2) := by
                  rw [map_neg, map_one]
                _ = algebraMap (ZMod 2) F (1 : ZMod 2) :=
                  congrArg (algebraMap (ZMod 2) F) hz
                _ = 1 := map_one _
            calc
              -(zeta ^ (2 ^ c.val)) =
                  (-1 : F) * (zeta ^ (2 ^ c.val)) := by rw [neg_one_mul]
              _ = 1 * (zeta ^ (2 ^ c.val)) := by rw [hnegOne]
              _ = zeta ^ (2 ^ c.val) := one_mul _
          exact hs.trans hneg
      have hac := primitiveRoot_singleWeight_injective hn zeta hprim hsingle
      exact Or.inl ⟨hac, hac⟩
    · rcases primitiveRoot_pairWeight_eq_pairWeight_candidates
          hn zeta hprim c c a b hab h.symm with hp | hp
      · exact Or.inl ⟨hp.1.symm, hp.2.symm⟩
      · exact Or.inr ⟨hp.2.symm, hp.1.symm⟩
  · exact primitiveRoot_pairWeight_eq_pairWeight_candidates
      hn zeta hprim a b c d hcd h

private theorem fieldGenerator_frobeniusWeight_injective
    {L : Type*} [Field L] [Finite L] [Algebra (ZMod 2) L]
    {m : ℕ} (lambda : L)
    (hfin : Module.finrank (ZMod 2) L = m)
    (hgen : Algebra.adjoin (ZMod 2) ({lambda} : Set L) = ⊤) :
    Function.Injective (fun i : Fin m => lambda ^ (2 ^ i.val)) := by
  let sigma := FiniteField.frobeniusAlgHom (ZMod 2) L
  have hfrob : Function.Injective (fun i : Fin m => sigma ^ i.val) := by
    intro i j hij
    have hcast : Fin.cast hfin.symm i = Fin.cast hfin.symm j := by
      apply (FiniteField.bijective_frobeniusAlgHom_pow (ZMod 2) L).1
      simpa [sigma] using hij
    exact Fin.cast_injective hfin.symm hcast
  intro i j hij
  apply hfrob
  apply AlgHom.ext_of_adjoin_eq_top hgen
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  simpa [sigma, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]
    using hij

/-- **Higman Lemma 11 (pp. 88--89), unequal-dimension pair-gap arithmetic.**

Let `lambda` generate a finite field `L/F₂` of degree `m`, without assuming
that it generates `Lˣ`.  Let `nu = lambda ^ (1 + 2^r)` be primitive of order
`2^n - 1`.  If a first-layer pair weight equals a Frobenius conjugate of
`nu`, then the two first-layer indices differ by `±r` modulo `m`.

No assumption that `m = n`, and no faithfulness assumption for the
second-layer action, is used. -/
theorem higmanLemmaEleven_pairGap_of_pairWeight_eq_frobeniusShift
    {L : Type*} [Field L] [Finite L] [Algebra (ZMod 2) L]
    {m n : ℕ} [NeZero m]
    (hn : 2 ≤ n) (lambda nu : L)
    (hfin : Module.finrank (ZMod 2) L = m)
    (hgen : Algebra.adjoin (ZMod 2) ({lambda} : Set L) = ⊤)
    (r i j : Fin m) (s : Fin n)
    (hnu : nu = lambda ^ (1 + 2 ^ r.val))
    (hprimNu : IsPrimitiveRoot nu (2 ^ n - 1))
    (hweight : lambda ^ (2 ^ i.val + 2 ^ j.val) =
      nu ^ (2 ^ s.val)) :
    HasHigmanPairGap (ZMod.finEquiv m r) i j := by
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := NeZero.pos m
  have hlambdaNe : lambda ≠ 0 := by
    intro hlambda
    have hnuZero : nu = 0 := by simp [hnu, hlambda]
    have hqpos : 0 < 2 ^ n - 1 := by
      have : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by omega)
      omega
    have hnuOne : nu ^ (2 ^ n - 1) = 1 := hprimNu.pow_eq_one
    rw [hnuZero, zero_pow hqpos.ne'] at hnuOne
    exact zero_ne_one hnuOne
  haveI : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card L = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2), hfin]
    norm_num [Nat.card_eq_fintype_card]
  have hlambdaPeriod : lambda ^ (2 ^ m - 1) = 1 := by
    rw [← hcard]
    exact FiniteField.pow_card_sub_one_eq_one lambda hlambdaNe
  have horderDvd : 2 ^ n - 1 ∣ orderOf lambda := by
    calc
      2 ^ n - 1 = orderOf nu := hprimNu.eq_orderOf
      _ = orderOf (lambda ^ (1 + 2 ^ r.val)) := by rw [hnu]
      _ ∣ orderOf lambda := orderOf_pow_dvd _
  have hweightLambda :
      lambda ^ (2 ^ i.val + 2 ^ j.val) =
        lambda ^ (2 ^ (r.val + s.val) + 2 ^ s.val) := by
    calc
      lambda ^ (2 ^ i.val + 2 ^ j.val) = nu ^ (2 ^ s.val) := hweight
      _ = (lambda ^ (1 + 2 ^ r.val)) ^ (2 ^ s.val) := by rw [hnu]
      _ = lambda ^ ((1 + 2 ^ r.val) * 2 ^ s.val) := by rw [pow_mul]
      _ = lambda ^ (2 ^ (r.val + s.val) + 2 ^ s.val) := by
        congr 1
        rw [add_mul, one_mul, ← pow_add]
        omega
  have hraw : Nat.ModEq (2 ^ n - 1)
      (2 ^ i.val + 2 ^ j.val)
      (2 ^ (r.val + s.val) + 2 ^ s.val) := by
    have hfinite : IsOfFinOrder lambda := by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨2 ^ m - 1, by
        have : 1 < 2 ^ m := Nat.one_lt_pow (by omega) (by omega)
        omega, hlambdaPeriod⟩
    exact (hfinite.pow_eq_pow_iff_modEq.mp hweightLambda).of_dvd horderDvd
  let ai : Fin n := residueFin hn0 i.val
  let bj : Fin n := residueFin hn0 j.val
  let crs : Fin n := residueFin hn0 (r.val + s.val)
  have hsred : residueFin hn0 s.val = s := by
    apply Fin.ext
    simp [residueFin, Nat.mod_eq_of_lt s.isLt]
  have hred : Nat.ModEq (2 ^ n - 1)
      (2 ^ ai.val + 2 ^ bj.val) (2 ^ crs.val + 2 ^ s.val) := by
    have hleft := (twoPower_modEq_mersenne_remainder hn0 (a := i.val)).add
      (twoPower_modEq_mersenne_remainder hn0 (a := j.val))
    have hright := (twoPower_modEq_mersenne_remainder hn0
      (a := r.val + s.val)).add
      (twoPower_modEq_mersenne_remainder hn0 (a := s.val))
    change Nat.ModEq (2 ^ n - 1)
      (2 ^ i.val + 2 ^ j.val) (2 ^ ai.val + 2 ^ bj.val) at hleft
    change Nat.ModEq (2 ^ n - 1)
      (2 ^ (r.val + s.val) + 2 ^ s.val)
      (2 ^ crs.val + 2 ^ (residueFin hn0 s.val).val) at hright
    rw [hsred] at hright
    exact hleft.symm.trans (hraw.trans hright)
  have hredWeight :
      nu ^ (2 ^ ai.val + 2 ^ bj.val) =
        nu ^ (2 ^ crs.val + 2 ^ s.val) :=
    pow_eq_pow_of_modEq hred hprimNu.pow_eq_one
  have hpairs := primitiveRoot_pairWeight_eq_pairWeight_candidates_all
    hn nu hprimNu ai bj crs s hredWeight
  have hgenInj := fieldGenerator_frobeniusWeight_injective lambda hfin hgen
  rcases hpairs with hp | hp
  · have hjmod : Nat.ModEq n j.val s.val := by
      change j.val % n = s.val % n
      have := congrArg Fin.val hp.2
      simpa [bj, residueFin, Nat.mod_eq_of_lt s.isLt] using this
    have hnuShift : nu ^ (2 ^ s.val) = nu ^ (2 ^ j.val) :=
      pow_eq_pow_of_modEq
        (twoPower_modEq_mersenne_of_index_modEq hn0 hjmod).symm
        hprimNu.pow_eq_one
    have hcyclic : lambda ^ (2 ^ (r.val + j.val)) =
        lambda ^ (2 ^ (r + j).val) :=
      pow_eq_pow_of_modEq (twoPower_cyclicAdd_modEq' r j) hlambdaPeriod
    have hexpand : nu ^ (2 ^ j.val) =
        lambda ^ (2 ^ (r + j).val + 2 ^ j.val) := by
      calc
        nu ^ (2 ^ j.val) =
            (lambda ^ (1 + 2 ^ r.val)) ^ (2 ^ j.val) := by rw [hnu]
        _ = lambda ^ ((1 + 2 ^ r.val) * 2 ^ j.val) := by rw [pow_mul]
        _ = lambda ^ (2 ^ (r.val + j.val) + 2 ^ j.val) := by
          congr 1
          rw [add_mul, one_mul, ← pow_add]
          omega
        _ = lambda ^ (2 ^ (r.val + j.val)) * lambda ^ (2 ^ j.val) := by
          rw [pow_add]
        _ = lambda ^ (2 ^ (r + j).val) * lambda ^ (2 ^ j.val) := by
          rw [hcyclic]
        _ = lambda ^ (2 ^ (r + j).val + 2 ^ j.val) := by rw [pow_add]
    have hprod : lambda ^ (2 ^ i.val) * lambda ^ (2 ^ j.val) =
        lambda ^ (2 ^ (r + j).val) * lambda ^ (2 ^ j.val) := by
      rw [← pow_add, ← pow_add]
      exact hweight.trans (hnuShift.trans hexpand)
    have hsingle : lambda ^ (2 ^ i.val) =
        lambda ^ (2 ^ (r + j).val) :=
      mul_right_cancel₀ (pow_ne_zero _ hlambdaNe) hprod
    have hi : i = r + j := hgenInj hsingle
    right
    simp only [higmanCyclicGap, hi, map_add]
    ring
  · have himod : Nat.ModEq n i.val s.val := by
      change i.val % n = s.val % n
      have := congrArg Fin.val hp.1
      simpa [ai, residueFin, Nat.mod_eq_of_lt s.isLt] using this
    have hnuShift : nu ^ (2 ^ s.val) = nu ^ (2 ^ i.val) :=
      pow_eq_pow_of_modEq
        (twoPower_modEq_mersenne_of_index_modEq hn0 himod).symm
        hprimNu.pow_eq_one
    have hcyclic : lambda ^ (2 ^ (r.val + i.val)) =
        lambda ^ (2 ^ (r + i).val) :=
      pow_eq_pow_of_modEq (twoPower_cyclicAdd_modEq' r i) hlambdaPeriod
    have hexpand : nu ^ (2 ^ i.val) =
        lambda ^ (2 ^ i.val + 2 ^ (r + i).val) := by
      calc
        nu ^ (2 ^ i.val) =
            (lambda ^ (1 + 2 ^ r.val)) ^ (2 ^ i.val) := by rw [hnu]
        _ = lambda ^ ((1 + 2 ^ r.val) * 2 ^ i.val) := by rw [pow_mul]
        _ = lambda ^ (2 ^ i.val + 2 ^ (r.val + i.val)) := by
          congr 1
          rw [add_mul, one_mul, ← pow_add]
        _ = lambda ^ (2 ^ i.val) * lambda ^ (2 ^ (r.val + i.val)) := by
          rw [pow_add]
        _ = lambda ^ (2 ^ i.val) * lambda ^ (2 ^ (r + i).val) := by
          rw [hcyclic]
        _ = lambda ^ (2 ^ i.val + 2 ^ (r + i).val) := by rw [pow_add]
    have hprod : lambda ^ (2 ^ i.val) * lambda ^ (2 ^ j.val) =
        lambda ^ (2 ^ i.val) * lambda ^ (2 ^ (r + i).val) := by
      rw [← pow_add, ← pow_add]
      exact hweight.trans (hnuShift.trans hexpand)
    have hsingle : lambda ^ (2 ^ j.val) =
        lambda ^ (2 ^ (r + i).val) := by
      apply mul_left_cancel₀ (pow_ne_zero _ hlambdaNe)
      exact hprod
    have hj : j = r + i := hgenInj hsingle
    left
    simp only [higmanCyclicGap, hj, map_add]
    ring

private theorem eigenvalue_eq_of_basis_repr_ne_zero
    {F W I : Type*} [Field F] [AddCommGroup W] [Module F W]
    [Finite I]
    (T : Module.End F W) (b : Basis I F W) (weight : I → F)
    (hb : ∀ i, T (b i) = weight i • b i)
    {x : W} {a : F} (hx : T x = a • x)
    (i : I) (hi : b.repr x i ≠ 0) :
    a = weight i := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  have hcoord : b.repr (T x) i = weight i * b.repr x i := by
    rw [← b.sum_repr x, map_sum]
    simp [hb, smul_smul, mul_comm]
    simp only [Finsupp.single_apply]
    simp
  have hcoord' := congrArg (fun y : W => b.repr y i) hx
  rw [hcoord] at hcoord'
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord'
  exact (mul_right_cancel₀ hi hcoord').symm

local instance higmanLemmaElevenLayerIsMulCommutative
    (H : Type uGroup) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

noncomputable local instance higmanLemmaElevenLayerZModTwoModule
    (H : Type uGroup) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 11 (p. 88), nonzero bracket seed.**

The full span of the actual lower-central commutator supplies a nonzero
bracket of two vectors in the canonical first-layer conjugate basis.  A
nonzero coordinate in the canonical second-layer basis then identifies its
exact actor weight.  No gap, primitive-root, or equal-degree assumption is
used at this selection step. -/
theorem exists_lowerCentralConjugateBasisBracketCoordinate
    {K : Type uK} {L : Type uL} {H C : Type uGroup}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [Group H] [Group C]
    (phi : C →* MulAut H) (c : C)
    (eOne : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] L)
    (lambda : L)
    (hcompatOne : ∀ v,
      eOne (lowerCentralLayerRepresentation phi 0 c v) =
        lambda * eOne v)
    (eTwo : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] K)
    (nu : K) (iota : K →ₐ[ZMod 2] L)
    (hcompatTwo : ∀ v,
      eTwo (lowerCentralLayerRepresentation phi 1 c v) = nu * eTwo v) :
    let bOne := conjugateTensorBasisOfLinearEquiv L eOne
    let bTwo := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo
    ∃ i j s,
      lowerCentralCommutatorBilinearBaseChange L H
          (bOne i) (bOne j) ≠ 0 ∧
      bTwo.repr
          (lowerCentralCommutatorBilinearBaseChange L H
            (bOne i) (bOne j)) s ≠ 0 ∧
      lambda ^ (2 ^ i.val + 2 ^ j.val) =
        (iota nu) ^ (2 ^ s.val) := by
  classical
  let bOne := conjugateTensorBasisOfLinearEquiv L eOne
  let bTwo := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo
  let TOne : Module.End L
      (L ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) :=
    (lowerCentralLayerRepresentation phi 0 c).baseChange L
  let TTwo : Module.End L
      (L ⊗[ZMod 2] Additive (lowerCentralLayer H 1)) :=
    (lowerCentralLayerRepresentation phi 1 c).baseChange L
  let beta := lowerCentralCommutatorBilinearBaseChange L H
  have hbOne (i : Fin (finrank (ZMod 2) L)) :
      TOne (bOne i) = lambda ^ (2 ^ i.val) • bOne i := by
    exact baseChange_eigen_conjugateTensorBasisOfLinearEquiv
      L eOne (lowerCentralLayerRepresentation phi 0 c)
      lambda hcompatOne i
  have hbTwo (s : Fin (finrank (ZMod 2) K)) :
      TTwo (bTwo s) = (iota nu) ^ (2 ^ s.val) • bTwo s := by
    simpa only [map_pow] using
      (baseChange_eigen_conjugateTensorBasisAlongOfLinearEquiv
        K L iota eTwo (lowerCentralLayerRepresentation phi 1 c)
        nu hcompatTwo s)
  have hbracket : ∃ i j : Fin (finrank (ZMod 2) L),
      beta (bOne i) (bOne j) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hnone' : ∀ i j : Fin (finrank (ZMod 2) L),
        beta (bOne i) (bOne j) = 0 := hnone
    have hmap2 : Submodule.map₂ beta ⊤ ⊤ ≤ ⊥ := by
      rw [← bOne.span_eq, Submodule.map₂_span_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      change beta (bOne i) (bOne j) = 0
      exact hnone' i j
    have hspan := lowerCentralCommutatorBilinearBaseChange_span_eq_top L H
    have htopBot : (⊤ : Submodule L
        (L ⊗[ZMod 2] Additive (lowerCentralLayer H 1))) = ⊥ := by
      rw [← hspan]
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨z, rfl⟩
        exact hmap2
          (Submodule.apply_mem_map₂ beta Submodule.mem_top Submodule.mem_top)
      · exact bot_le
    let s0 : Fin (finrank (ZMod 2) K) := ⟨0, Module.finrank_pos⟩
    have hbmem : bTwo s0 ∈ (⊥ : Submodule L
        (L ⊗[ZMod 2] Additive (lowerCentralLayer H 1))) := by
      rw [← htopBot]
      exact Submodule.mem_top
    have hbzero : bTwo s0 = 0 := by simpa using hbmem
    exact bTwo.ne_zero s0 hbzero
  obtain ⟨i, j, hij⟩ := hbracket
  let z := beta (bOne i) (bOne j)
  have hz : z ≠ 0 := by simpa only [z] using hij
  have hzrepr : bTwo.repr z ≠ 0 := by
    intro hzero
    apply hz
    apply bTwo.repr.injective
    simpa only [map_zero] using hzero
  obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hzrepr
  simp only [Finsupp.zero_apply] at hs
  have hzEigen :
      TTwo z = lambda ^ (2 ^ i.val + 2 ^ j.val) • z := by
    simpa only [TOne, TTwo, beta, z, ← pow_add] using
      (lowerCentralCommutatorBilinearBaseChange_eigenweight
        L phi c
        (lambda ^ (2 ^ i.val)) (lambda ^ (2 ^ j.val))
        (bOne i) (bOne j) (hbOne i) (hbOne j))
  refine ⟨i, j, s, hij, ?_, ?_⟩
  · simpa only [beta, z] using hs
  · exact eigenvalue_eq_of_basis_repr_ne_zero
      TTwo bTwo (fun t => (iota nu) ^ (2 ^ t.val)) hbTwo
      hzEigen s hs

/-- **Higman Lemma 11 (pp. 88--89), actual bracket-support step.**

Every nonzero value of the actual first lower-central commutator pairing on
the canonical first-layer conjugate basis has Higman's single cyclic gap.
The first- and second-layer field degrees remain distinct. -/
theorem lowerCentralPairGapSupport_of_commonConjugateBases
    {K : Type uK} {L : Type uL} {H C : Type uGroup}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [Group H] [Group C] [NeZero (finrank (ZMod 2) L)]
    (phi : C →* MulAut H) (c : C)
    (eOne : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] L)
    (lambda : L)
    (hgen : Algebra.adjoin (ZMod 2) ({lambda} : Set L) = ⊤)
    (hcompatOne : ∀ v,
      eOne (lowerCentralLayerRepresentation phi 0 c v) =
        lambda * eOne v)
    (eTwo : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] K)
    (nu : K) (iota : K →ₐ[ZMod 2] L)
    (hcompatTwo : ∀ v,
      eTwo (lowerCentralLayerRepresentation phi 1 c v) = nu * eTwo v)
    (hn : 2 ≤ finrank (ZMod 2) K)
    (hprimNu : IsPrimitiveRoot nu (2 ^ finrank (ZMod 2) K - 1))
    (r : Fin (finrank (ZMod 2) L))
    (hnu : iota nu = lambda ^ (1 + 2 ^ r.val)) :
    let bOne := conjugateTensorBasisOfLinearEquiv L eOne
    ∀ i j : Fin (finrank (ZMod 2) L),
      lowerCentralCommutatorBilinearBaseChange L H
          (bOne i) (bOne j) ≠ 0 →
        HasHigmanPairGap
          (ZMod.finEquiv (finrank (ZMod 2) L) r) i j := by
  let bOne := conjugateTensorBasisOfLinearEquiv L eOne
  let bTwo := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo
  let TOne : Module.End L
      (L ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) :=
    (lowerCentralLayerRepresentation phi 0 c).baseChange L
  let TTwo : Module.End L
      (L ⊗[ZMod 2] Additive (lowerCentralLayer H 1)) :=
    (lowerCentralLayerRepresentation phi 1 c).baseChange L
  have hbOne (i : Fin (finrank (ZMod 2) L)) :
      TOne (bOne i) = lambda ^ (2 ^ i.val) • bOne i := by
    exact baseChange_eigen_conjugateTensorBasisOfLinearEquiv
      L eOne (lowerCentralLayerRepresentation phi 0 c)
      lambda hcompatOne i
  have hbTwo (s : Fin (finrank (ZMod 2) K)) :
      TTwo (bTwo s) = (iota nu) ^ (2 ^ s.val) • bTwo s := by
    simpa only [map_pow] using
      (baseChange_eigen_conjugateTensorBasisAlongOfLinearEquiv
        K L iota eTwo (lowerCentralLayerRepresentation phi 1 c)
        nu hcompatTwo s)
  change ∀ i j,
    lowerCentralCommutatorBilinearBaseChange L H
        (bOne i) (bOne j) ≠ 0 →
      HasHigmanPairGap
        (ZMod.finEquiv (finrank (ZMod 2) L) r) i j
  intro i j hbracket
  let z := lowerCentralCommutatorBilinearBaseChange L H
    (bOne i) (bOne j)
  have hz : z ≠ 0 := by simpa only [z] using hbracket
  have hzEigen :
      TTwo z = lambda ^ (2 ^ i.val + 2 ^ j.val) • z := by
    simpa only [TOne, TTwo, z, ← pow_add] using
      (lowerCentralCommutatorBilinearBaseChange_eigenweight
        L phi c
        (lambda ^ (2 ^ i.val)) (lambda ^ (2 ^ j.val))
        (bOne i) (bOne j) (hbOne i) (hbOne j))
  have hzrepr : bTwo.repr z ≠ 0 := by
    intro hzero
    apply hz
    apply bTwo.repr.injective
    simpa only [map_zero] using hzero
  obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hzrepr
  simp only [Finsupp.zero_apply] at hs
  have hweight :
      lambda ^ (2 ^ i.val + 2 ^ j.val) =
        (iota nu) ^ (2 ^ s.val) :=
    eigenvalue_eq_of_basis_repr_ne_zero
      TTwo bTwo (fun t => (iota nu) ^ (2 ^ t.val)) hbTwo
      hzEigen s hs
  exact higmanLemmaEleven_pairGap_of_pairWeight_eq_frobeniusShift
    hn lambda (iota nu) rfl hgen r i j s hnu
    (hprimNu.map_of_injective iota.injective) hweight

/-- **Higman Lemma 11 (p. 89), normalized bracket axis.**

Once the selected first-layer bracket has normalized weight
`iota nu = lambda^(1 + 2^r)`, it lies on the zeroth second-layer Frobenius
eigenline.  Thus it is a nonzero scalar multiple of the zeroth canonical
second-layer basis vector. -/
theorem exists_ne_zero_smul_secondConjugateBasis_zero_of_bracket
    {K : Type uK} {L : Type uL} {H C : Type uGroup}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [Group H] [Group C]
    [NeZero (finrank (ZMod 2) K)]
    [NeZero (finrank (ZMod 2) L)]
    (phi : C →* MulAut H) (c : C)
    (eOne : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] L)
    (lambda : L)
    (hcompatOne : ∀ v,
      eOne (lowerCentralLayerRepresentation phi 0 c v) =
        lambda * eOne v)
    (eTwo : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] K)
    (nu : K) (iota : K →ₐ[ZMod 2] L)
    (hcompatTwo : ∀ v,
      eTwo (lowerCentralLayerRepresentation phi 1 c v) = nu * eTwo v)
    (hn : 2 ≤ finrank (ZMod 2) K)
    (hprimNu : IsPrimitiveRoot nu
      (2 ^ finrank (ZMod 2) K - 1))
    (r : Fin (finrank (ZMod 2) L))
    (hnu : iota nu = lambda ^ (1 + 2 ^ r.val))
    (hbracket :
      let bOne := conjugateTensorBasisOfLinearEquiv L eOne
      lowerCentralCommutatorBilinearBaseChange L H
        (bOne 0) (bOne r) ≠ 0) :
    let bOne := conjugateTensorBasisOfLinearEquiv L eOne
    let bTwo := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo
    ∃ epsilon : L, epsilon ≠ 0 ∧
      lowerCentralCommutatorBilinearBaseChange L H
        (bOne 0) (bOne r) = epsilon • bTwo 0 := by
  classical
  let bOne := conjugateTensorBasisOfLinearEquiv L eOne
  let bTwo := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo
  let TOne : Module.End L
      (L ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) :=
    (lowerCentralLayerRepresentation phi 0 c).baseChange L
  let TTwo : Module.End L
      (L ⊗[ZMod 2] Additive (lowerCentralLayer H 1)) :=
    (lowerCentralLayerRepresentation phi 1 c).baseChange L
  let z := lowerCentralCommutatorBilinearBaseChange L H
    (bOne 0) (bOne r)
  have hbOne (i : Fin (finrank (ZMod 2) L)) :
      TOne (bOne i) = lambda ^ (2 ^ i.val) • bOne i := by
    exact baseChange_eigen_conjugateTensorBasisOfLinearEquiv
      L eOne (lowerCentralLayerRepresentation phi 0 c)
      lambda hcompatOne i
  have hbTwo (s : Fin (finrank (ZMod 2) K)) :
      TTwo (bTwo s) = (iota nu) ^ (2 ^ s.val) • bTwo s := by
    simpa only [map_pow] using
      (baseChange_eigen_conjugateTensorBasisAlongOfLinearEquiv
        K L iota eTwo (lowerCentralLayerRepresentation phi 1 c)
        nu hcompatTwo s)
  have hz : z ≠ 0 := by simpa only [z, bOne] using hbracket
  have hzEigen : TTwo z = (iota nu) • z := by
    have hraw := lowerCentralCommutatorBilinearBaseChange_eigenweight
      L phi c lambda (lambda ^ (2 ^ r.val))
      (bOne 0) (bOne r) (by simpa using hbOne 0) (hbOne r)
    have hweight : lambda * lambda ^ (2 ^ r.val) = iota nu := by
      calc
        lambda * lambda ^ (2 ^ r.val) =
            lambda ^ (1 + 2 ^ r.val) := by rw [pow_add, pow_one]
        _ = iota nu := hnu.symm
    simpa only [TTwo, z, hweight] using hraw
  have hweightInj : Function.Injective
      (fun s : Fin (finrank (ZMod 2) K) =>
        (iota nu) ^ (2 ^ s.val)) :=
    primitiveRoot_singleWeight_injective hn (iota nu)
      (hprimNu.map_of_injective iota.injective)
  have hcoordZero (s : Fin (finrank (ZMod 2) K)) (hs : s ≠ 0) :
      bTwo.repr z s = 0 := by
    by_contra hscoord
    have hweight := eigenvalue_eq_of_basis_repr_ne_zero
      TTwo bTwo (fun t => (iota nu) ^ (2 ^ t.val)) hbTwo
      hzEigen s hscoord
    have hsZero : (0 : Fin (finrank (ZMod 2) K)) = s := by
      apply hweightInj
      simpa using hweight
    exact hs hsZero.symm
  let epsilon : L := bTwo.repr z 0
  have hepsilon : epsilon ≠ 0 := by
    intro hepsilonZero
    apply hz
    apply bTwo.repr.injective
    ext s
    simp only [map_zero, Finsupp.zero_apply]
    by_cases hs : s = 0
    · subst s
      exact hepsilonZero
    · exact hcoordZero s hs
  refine ⟨epsilon, hepsilon, ?_⟩
  change z = epsilon • bTwo 0
  apply bTwo.repr.injective
  ext s
  by_cases hs : s = 0
  · subst s
    simp [epsilon]
  · rw [hcoordZero s hs]
    simp [hs]

/-! ## Frobenius normalization of the selected bracket seed -/

private noncomputable def frobeniusLinearEquivForNormalization
    (K : Type uCommonField) [Field K] [Finite K] [Algebra (ZMod 2) K]
    (s : ℕ) : K ≃ₗ[ZMod 2] K :=
  ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ s).toLinearEquiv

private noncomputable def frobeniusShiftLinearEquivForNormalization
    {K : Type uCommonField} {V : Type uGroup}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] K) (s : ℕ) : V ≃ₗ[ZMod 2] K :=
  e.trans (frobeniusLinearEquivForNormalization K s)

@[simp] private theorem frobeniusShiftLinearEquivForNormalization_apply
    {K : Type uCommonField} {V : Type uGroup}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] K) (s : ℕ) (v : V) :
    frobeniusShiftLinearEquivForNormalization e s v =
      (e v) ^ (2 ^ s) := by
  simp [frobeniusShiftLinearEquivForNormalization,
    frobeniusLinearEquivForNormalization, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate]

private theorem frobeniusShiftLinearEquivForNormalization_mul_compat
    {K : Type uCommonField} {V : Type uGroup}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [AddCommGroup V] [Module (ZMod 2) V]
    (T : Module.End (ZMod 2) V)
    (e : V ≃ₗ[ZMod 2] K) (lambda : K)
    (hcompat : ∀ v, e (T v) = lambda * e v) (s : ℕ) :
    ∀ v, frobeniusShiftLinearEquivForNormalization e s (T v) =
      lambda ^ (2 ^ s) *
        frobeniusShiftLinearEquivForNormalization e s v := by
  intro v
  simp only [frobeniusShiftLinearEquivForNormalization_apply,
    hcompat, mul_pow]

private theorem adjoin_frobeniusShiftForNormalization_eq_top
    {K : Type uCommonField} [Field K] [Finite K] [Algebra (ZMod 2) K]
    (lambda : K)
    (hgen : Algebra.adjoin (ZMod 2) ({lambda} : Set K) = ⊤)
    (s : ℕ) :
    Algebra.adjoin (ZMod 2) ({lambda ^ (2 ^ s)} : Set K) = ⊤ := by
  let sigma : K ≃ₐ[ZMod 2] K :=
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ s
  have hsigma : sigma lambda = lambda ^ (2 ^ s) := by
    simp [sigma, AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate]
  calc
    Algebra.adjoin (ZMod 2) ({lambda ^ (2 ^ s)} : Set K) =
        Algebra.adjoin (ZMod 2) ({sigma lambda} : Set K) := by rw [hsigma]
    _ = (Algebra.adjoin (ZMod 2) ({lambda} : Set K)).map
          sigma.toAlgHom :=
      (AlgHom.map_adjoin_singleton sigma.toAlgHom lambda).symm
    _ = ⊤ := by
      rw [hgen, Algebra.map_top,
        (AlgHom.range_eq_top _).mpr sigma.surjective]

private theorem primitiveRoot_frobeniusShiftForNormalization
    {K : Type uCommonField} [CommMonoid K] {lambda : K} {n : ℕ}
    (hn : 0 < n) (hprim : IsPrimitiveRoot lambda (2 ^ n - 1))
    (s : ℕ) :
    IsPrimitiveRoot (lambda ^ (2 ^ s)) (2 ^ n - 1) := by
  have hodd : Odd (2 ^ n - 1) := by
    rw [Nat.odd_iff]
    simpa using hn
  exact hprim.pow_of_coprime (2 ^ s)
    ((Nat.coprime_two_left.mpr hodd).pow_left s)

private theorem frobeniusPower_eq_of_fin_add_eq
    {K : Type uCommonField} [Field K] [Finite K] [Algebra (ZMod 2) K]
    [NeZero (finrank (ZMod 2) K)]
    (x : K)
    (i r j : Fin (finrank (ZMod 2) K)) (hij : i + r = j) :
    x ^ (2 ^ (i.val + r.val)) = x ^ (2 ^ j.val) := by
  let sigma := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  have hmod : Nat.ModEq (finrank (ZMod 2) K)
      (i.val + r.val) j.val := by
    change (i.val + r.val) % finrank (ZMod 2) K =
      j.val % finrank (ZMod 2) K
    rw [Nat.mod_eq_of_lt j.isLt]
    simpa only [Fin.val_add] using congrArg Fin.val hij
  have hsigma : sigma ^ (i.val + r.val) = sigma ^ j.val := by
    rw [pow_eq_pow_iff_modEq,
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    exact hmod
  have happly := DFunLike.congr_fun hsigma x
  simpa only [sigma, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    pow_iterate, ZMod.card] using happly

private theorem pairWeight_eq_shiftedGapWeight
    {K : Type uCommonField} [Field K] [Finite K] [Algebra (ZMod 2) K]
    [NeZero (finrank (ZMod 2) K)]
    (lambda : K) (i j : Fin (finrank (ZMod 2) K)) :
    let r := j - i
    (lambda ^ (2 ^ i.val)) ^ (1 + 2 ^ r.val) =
      lambda ^ (2 ^ i.val + 2 ^ j.val) := by
  let r := j - i
  have hir : i + r = j := by
    dsimp [r]
    rw [add_comm]
    exact sub_add_cancel j i
  have hcycle := frobeniusPower_eq_of_fin_add_eq lambda i r j hir
  dsimp [r] at hcycle ⊢
  calc
    (lambda ^ (2 ^ i.val)) ^ (1 + 2 ^ (j - i).val) =
        lambda ^ (2 ^ i.val * (1 + 2 ^ (j - i).val)) := by
          rw [pow_mul]
    _ = lambda ^ (2 ^ i.val + 2 ^ (i.val + (j - i).val)) := by
      congr 1
      rw [Nat.mul_add, mul_one, ← pow_add]
    _ = lambda ^ (2 ^ i.val + 2 ^ j.val) := by
      calc
        lambda ^ (2 ^ i.val + 2 ^ (i.val + (j - i).val)) =
            lambda ^ (2 ^ i.val) *
              lambda ^ (2 ^ (i.val + (j - i).val)) := pow_add _ _ _
        _ = lambda ^ (2 ^ i.val) * lambda ^ (2 ^ j.val) := by
          rw [hcycle]
        _ = lambda ^ (2 ^ i.val + 2 ^ j.val) := (pow_add _ _ _).symm

private theorem conjugateTensorBasis_repr_frobeniusBaseChange
    {K : Type uCommonField} [Field K] [Finite K] [Algebra (ZMod 2) K]
    [NeZero (finrank (ZMod 2) K)]
    (i q : Fin (finrank (ZMod 2) K)) (z : K ⊗[ZMod 2] K) :
    (conjugateTensorBasis K).repr
        ((frobeniusLinearEquivForNormalization K i.val).baseChange
          (ZMod 2) K K K z) q =
      (conjugateTensorBasis K).repr z (q + i) := by
  let sigma : K ≃ₐ[ZMod 2] K :=
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ i.val
  change (conjugateTensorBasis K).repr
      (sigma.toLinearEquiv.baseChange (ZMod 2) K K K z) q =
    (conjugateTensorBasis K).repr z (q + i)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
      have hsigma : sigma x = x ^ (2 ^ i.val) := by
        simp [sigma, AlgEquiv.coe_pow,
          FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate]
      have hcycle : x ^ (2 ^ (i.val + q.val)) =
          x ^ (2 ^ (q + i).val) :=
        frobeniusPower_eq_of_fin_add_eq x i q (q + i) (by
          simp [add_comm])
      simp only [LinearEquiv.baseChange_tmul,
        conjugateTensorBasis_repr_apply,
        frobeniusTensorCoordinates_tmul]
      change a * (sigma x) ^ (2 ^ q.val) =
        a * x ^ (2 ^ (q + i).val)
      rw [hsigma, ← pow_mul, ← pow_add, hcycle]

private theorem frobeniusBaseChange_conjugateTensorBasis_add
    {K : Type uCommonField} [Field K] [Finite K] [Algebra (ZMod 2) K]
    [NeZero (finrank (ZMod 2) K)]
    (i k : Fin (finrank (ZMod 2) K)) :
    (frobeniusLinearEquivForNormalization K i.val).baseChange
        (ZMod 2) K K K (conjugateTensorBasis K (i + k)) =
      conjugateTensorBasis K k := by
  apply (conjugateTensorBasis K).repr.injective
  ext q
  rw [conjugateTensorBasis_repr_frobeniusBaseChange]
  simp only [Basis.repr_self_apply]
  by_cases hkq : k = q
  · subst q
    simp [add_comm]
  · have hne : i + k ≠ i + q := fun h => hkq (add_left_cancel h)
    simp [hkq, hne, add_comm]

private theorem frobeniusBaseChange_symm_conjugateTensorBasis
    {K : Type uCommonField} [Field K] [Finite K] [Algebra (ZMod 2) K]
    [NeZero (finrank (ZMod 2) K)]
    (i k : Fin (finrank (ZMod 2) K)) :
    ((frobeniusLinearEquivForNormalization K i.val).baseChange
        (ZMod 2) K K K).symm (conjugateTensorBasis K k) =
      conjugateTensorBasis K (i + k) := by
  apply ((frobeniusLinearEquivForNormalization K i.val).baseChange
    (ZMod 2) K K K).injective
  rw [LinearEquiv.apply_symm_apply,
    frobeniusBaseChange_conjugateTensorBasis_add]

private theorem conjugateTensorBasisOf_frobeniusShift
    {K : Type uCommonField} {V : Type uGroup}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [NeZero (finrank (ZMod 2) K)]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] K)
    (i k : Fin (finrank (ZMod 2) K)) :
    conjugateTensorBasisOfLinearEquiv K
        (frobeniusShiftLinearEquivForNormalization e i.val) k =
      conjugateTensorBasisOfLinearEquiv K e (i + k) := by
  simp only [conjugateTensorBasisOfLinearEquiv, Basis.map_apply]
  rw [frobeniusShiftLinearEquivForNormalization,
    LinearEquiv.baseChange_trans]
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  rw [frobeniusBaseChange_symm_conjugateTensorBasis]

private theorem conjugateTensorBasisAlong_repr_frobeniusBaseChange
    {K : Type uK} {L : Type uL}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [Field L] [Algebra (ZMod 2) L]
    [NeZero (finrank (ZMod 2) K)]
    (iota : K →ₐ[ZMod 2] L)
    (i q : Fin (finrank (ZMod 2) K)) (z : L ⊗[ZMod 2] K) :
    (conjugateTensorBasisAlong K L iota).repr
        ((frobeniusLinearEquivForNormalization K i.val).baseChange
          (ZMod 2) L K K z) q =
      (conjugateTensorBasisAlong K L iota).repr z (q + i) := by
  let sigma : K ≃ₐ[ZMod 2] K :=
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ i.val
  change frobeniusTensorCoordinatesAlong K L iota
      (sigma.toLinearEquiv.baseChange (ZMod 2) L K K z) q =
    frobeniusTensorCoordinatesAlong K L iota z (q + i)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy]
  | tmul a x =>
      have hsigma : sigma x = x ^ (2 ^ i.val) := by
        simp [sigma, AlgEquiv.coe_pow,
          FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate]
      have hcycle : x ^ (2 ^ (i.val + q.val)) =
          x ^ (2 ^ (q + i).val) :=
        frobeniusPower_eq_of_fin_add_eq x i q (q + i) (by
          simp [add_comm])
      simp only [LinearEquiv.baseChange_tmul,
        frobeniusTensorCoordinatesAlong_tmul]
      change a * iota ((sigma x) ^ (2 ^ q.val)) =
        a * iota (x ^ (2 ^ (q + i).val))
      rw [hsigma, ← pow_mul, ← pow_add, hcycle]

private theorem conjugateTensorBasisAlongOf_frobeniusShift_repr
    {K : Type uK} {L : Type uL} {V : Type uGroup}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [Field L] [Algebra (ZMod 2) L]
    [NeZero (finrank (ZMod 2) K)]
    [AddCommGroup V] [Module (ZMod 2) V]
    (iota : K →ₐ[ZMod 2] L) (e : V ≃ₗ[ZMod 2] K)
    (i k : Fin (finrank (ZMod 2) K)) (z : L ⊗[ZMod 2] V) :
    (conjugateTensorBasisAlongOfLinearEquiv K L iota
        (frobeniusShiftLinearEquivForNormalization e i.val)).repr z k =
      (conjugateTensorBasisAlongOfLinearEquiv K L iota e).repr
        z (k + i) := by
  change (conjugateTensorBasisAlong K L iota).repr
      ((frobeniusShiftLinearEquivForNormalization e i.val).baseChange
        (ZMod 2) L V K z) k =
    (conjugateTensorBasisAlong K L iota).repr
      (e.baseChange (ZMod 2) L V K z) (k + i)
  rw [frobeniusShiftLinearEquivForNormalization,
    LinearEquiv.baseChange_trans]
  exact conjugateTensorBasisAlong_repr_frobeniusBaseChange
    iota i k (e.baseChange (ZMod 2) L V K z)

/-- **Higman Lemma 11 (pp. 88--89), normalized actual bracket data.**

Starting from the actual full-span lower-central bracket, rotate the two
finite-field models by Frobenius so that the selected nonzero bracket has
indices `(0, r)` in the first canonical basis and a nonzero zeroth coordinate
in the second.  The shifted generators retain all field-generation and
primitive-root properties, satisfy `iota nu' = lambda'^(1+2^r)`, and give the
single-gap law for every nonzero actual basis bracket.  This strong form also
records the exact second-layer Frobenius shift. -/
theorem exists_normalizedLowerCentralConjugateBasisBracketCoordinate_with_secondShift
    {K : Type uK} {L : Type uL} {H C : Type uGroup}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [Group H] [Group C]
    [NeZero (finrank (ZMod 2) K)]
    [NeZero (finrank (ZMod 2) L)]
    (phi : C →* MulAut H) (c : C)
    (eOne : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] L)
    (lambda : L)
    (hgen : Algebra.adjoin (ZMod 2) ({lambda} : Set L) = ⊤)
    (hcompatOne : ∀ v,
      eOne (lowerCentralLayerRepresentation phi 0 c v) =
        lambda * eOne v)
    (eTwo : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] K)
    (nu : K) (iota : K →ₐ[ZMod 2] L)
    (hcompatTwo : ∀ v,
      eTwo (lowerCentralLayerRepresentation phi 1 c v) = nu * eTwo v)
    (hn : 2 ≤ finrank (ZMod 2) K)
    (hprimNu : IsPrimitiveRoot nu
      (2 ^ finrank (ZMod 2) K - 1)) :
    ∃ (s : Fin (finrank (ZMod 2) K))
      (eOne' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] L)
      (eTwo' : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] K)
      (lambda' : L) (nu' : K)
      (r : Fin (finrank (ZMod 2) L)),
      eTwo' = eTwo.trans
        (((FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod 2) K) ^ s.val).toLinearEquiv) ∧
      (∀ v, eOne' (lowerCentralLayerRepresentation phi 0 c v) =
        lambda' * eOne' v) ∧
      Algebra.adjoin (ZMod 2) ({lambda'} : Set L) = ⊤ ∧
      (∀ v, eTwo' (lowerCentralLayerRepresentation phi 1 c v) =
        nu' * eTwo' v) ∧
      IsPrimitiveRoot nu' (2 ^ finrank (ZMod 2) K - 1) ∧
      iota nu' = lambda' ^ (1 + 2 ^ r.val) ∧
      r ≠ 0 ∧
      let bOne' := conjugateTensorBasisOfLinearEquiv L eOne'
      let bTwo' := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo'
      lowerCentralCommutatorBilinearBaseChange L H
          (bOne' 0) (bOne' r) ≠ 0 ∧
      bTwo'.repr
          (lowerCentralCommutatorBilinearBaseChange L H
            (bOne' 0) (bOne' r)) 0 ≠ 0 ∧
      ∀ a b : Fin (finrank (ZMod 2) L),
        lowerCentralCommutatorBilinearBaseChange L H
            (bOne' a) (bOne' b) ≠ 0 →
          HasHigmanPairGap
            (ZMod.finEquiv (finrank (ZMod 2) L) r) a b := by
  classical
  let bOne := conjugateTensorBasisOfLinearEquiv L eOne
  let bTwo := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo
  let beta := lowerCentralCommutatorBilinearBaseChange L H
  obtain ⟨i, j, s, hbracket, hcoordinate, hweight⟩ :=
    exists_lowerCentralConjugateBasisBracketCoordinate
      phi c eOne lambda hcompatOne eTwo nu iota hcompatTwo
  let r := j - i
  let eOne' := frobeniusShiftLinearEquivForNormalization eOne i.val
  let eTwo' := frobeniusShiftLinearEquivForNormalization eTwo s.val
  let lambda' := lambda ^ (2 ^ i.val)
  let nu' := nu ^ (2 ^ s.val)
  have hcompatOne' : ∀ v,
      eOne' (lowerCentralLayerRepresentation phi 0 c v) =
        lambda' * eOne' v := by
    exact frobeniusShiftLinearEquivForNormalization_mul_compat
      (lowerCentralLayerRepresentation phi 0 c)
      eOne lambda hcompatOne i.val
  have hcompatTwo' : ∀ v,
      eTwo' (lowerCentralLayerRepresentation phi 1 c v) =
        nu' * eTwo' v := by
    exact frobeniusShiftLinearEquivForNormalization_mul_compat
      (lowerCentralLayerRepresentation phi 1 c)
      eTwo nu hcompatTwo s.val
  have hgen' : Algebra.adjoin (ZMod 2) ({lambda'} : Set L) = ⊤ :=
    adjoin_frobeniusShiftForNormalization_eq_top lambda hgen i.val
  have hprimNu' : IsPrimitiveRoot nu'
      (2 ^ finrank (ZMod 2) K - 1) :=
    primitiveRoot_frobeniusShiftForNormalization (by omega) hprimNu s.val
  have hweight' : lambda ^ (2 ^ i.val + 2 ^ j.val) =
      iota (nu ^ (2 ^ s.val)) := by
    rw [map_pow]
    exact hweight
  have hnormal : lambda' ^ (1 + 2 ^ r.val) = iota nu' := by
    exact (pairWeight_eq_shiftedGapWeight lambda i j).trans hweight'
  have hnu : iota nu' = lambda' ^ (1 + 2 ^ r.val) := hnormal.symm
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hbracket
      (lowerCentralCommutatorBilinearBaseChange_self L H (bOne i))
  have hr : r ≠ 0 := by
    intro hr
    dsimp [r] at hr
    exact hij (sub_eq_zero.mp hr).symm
  have hir : i + r = j := by
    dsimp [r]
    rw [add_comm]
    exact sub_add_cancel j i
  let bOne' := conjugateTensorBasisOfLinearEquiv L eOne'
  let bTwo' := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo'
  have hbOneZero : bOne' 0 = bOne i := by
    simpa [bOne', bOne, eOne'] using
      (conjugateTensorBasisOf_frobeniusShift eOne i 0)
  have hbOneR : bOne' r = bOne j := by
    calc
      bOne' r = bOne (i + r) := by
        simpa [bOne', bOne, eOne'] using
          (conjugateTensorBasisOf_frobeniusShift eOne i r)
      _ = bOne j := congrArg bOne hir
  have hbracket' : beta (bOne' 0) (bOne' r) ≠ 0 := by
    simpa only [hbOneZero, hbOneR] using hbracket
  let z := beta (bOne i) (bOne j)
  have hrepr : bTwo'.repr z 0 = bTwo.repr z s := by
    simpa [bTwo', bTwo, eTwo', z] using
      (conjugateTensorBasisAlongOf_frobeniusShift_repr
        iota eTwo s 0 z)
  have hcoordinate' :
      bTwo'.repr (beta (bOne' 0) (bOne' r)) 0 ≠ 0 := by
    rw [hbOneZero, hbOneR]
    change bTwo'.repr z 0 ≠ 0
    rw [hrepr]
    exact hcoordinate
  have hgap : ∀ a b : Fin (finrank (ZMod 2) L),
      beta (bOne' a) (bOne' b) ≠ 0 →
        HasHigmanPairGap
          (ZMod.finEquiv (finrank (ZMod 2) L) r) a b := by
    exact lowerCentralPairGapSupport_of_commonConjugateBases
      phi c eOne' lambda' hgen' hcompatOne'
      eTwo' nu' iota hcompatTwo' hn hprimNu' r hnu
  refine ⟨s, eOne', eTwo', lambda', nu', r, ?_,
    hcompatOne', hgen', hcompatTwo', hprimNu', hnu, hr, ?_⟩
  · rfl
  · exact ⟨hbracket', hcoordinate', hgap⟩

/-- Compatibility projection of the shift-tracking normalized bracket data.
This preserves the original public signature while forgetting the explicit
second-layer Frobenius shift. -/
theorem exists_normalizedLowerCentralConjugateBasisBracketCoordinate
    {K : Type uK} {L : Type uL} {H C : Type uGroup}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [Group H] [Group C]
    [NeZero (finrank (ZMod 2) K)]
    [NeZero (finrank (ZMod 2) L)]
    (phi : C →* MulAut H) (c : C)
    (eOne : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] L)
    (lambda : L)
    (hgen : Algebra.adjoin (ZMod 2) ({lambda} : Set L) = ⊤)
    (hcompatOne : ∀ v,
      eOne (lowerCentralLayerRepresentation phi 0 c v) =
        lambda * eOne v)
    (eTwo : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] K)
    (nu : K) (iota : K →ₐ[ZMod 2] L)
    (hcompatTwo : ∀ v,
      eTwo (lowerCentralLayerRepresentation phi 1 c v) = nu * eTwo v)
    (hn : 2 ≤ finrank (ZMod 2) K)
    (hprimNu : IsPrimitiveRoot nu
      (2 ^ finrank (ZMod 2) K - 1)) :
    ∃ (eOne' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] L)
      (eTwo' : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] K)
      (lambda' : L) (nu' : K)
      (r : Fin (finrank (ZMod 2) L)),
      (∀ v, eOne' (lowerCentralLayerRepresentation phi 0 c v) =
        lambda' * eOne' v) ∧
      Algebra.adjoin (ZMod 2) ({lambda'} : Set L) = ⊤ ∧
      (∀ v, eTwo' (lowerCentralLayerRepresentation phi 1 c v) =
        nu' * eTwo' v) ∧
      IsPrimitiveRoot nu' (2 ^ finrank (ZMod 2) K - 1) ∧
      iota nu' = lambda' ^ (1 + 2 ^ r.val) ∧
      r ≠ 0 ∧
      let bOne' := conjugateTensorBasisOfLinearEquiv L eOne'
      let bTwo' := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo'
      lowerCentralCommutatorBilinearBaseChange L H
          (bOne' 0) (bOne' r) ≠ 0 ∧
      bTwo'.repr
          (lowerCentralCommutatorBilinearBaseChange L H
            (bOne' 0) (bOne' r)) 0 ≠ 0 ∧
      ∀ a b : Fin (finrank (ZMod 2) L),
        lowerCentralCommutatorBilinearBaseChange L H
            (bOne' a) (bOne' b) ≠ 0 →
          HasHigmanPairGap
            (ZMod.finEquiv (finrank (ZMod 2) L) r) a b := by
  obtain ⟨_, eOne', eTwo', lambda', nu', r, _,
      hcompatOne', hgen', hcompatTwo', hprimNu', hnu, hr, hbracket⟩ :=
    exists_normalizedLowerCentralConjugateBasisBracketCoordinate_with_secondShift
      phi c eOne lambda hgen hcompatOne eTwo nu iota hcompatTwo hn hprimNu
  exact ⟨eOne', eTwo', lambda', nu', r,
    hcompatOne', hgen', hcompatTwo', hprimNu', hnu, hr, hbracket⟩

end OddOrder.Higman.Suzuki2Groups
