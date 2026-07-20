/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven.PairGap
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Higman's Lemma 11: the trace formula

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 11, pp. 88--89.

After the unique nonzero bracket gap has been normalized to `(0, r)`,
Higman's proof excludes `m = 2r`, recovers every cyclic-edge coefficient
by Frobenius, and rewrites the upper-triangular square sum as
`Tr[L/K](α * α^(2^r) * ε)`. This leaf formalizes precisely that step;
the proper-extension contradiction using Lemma 10 remains downstream.
-/
set_option autoImplicit false

open scoped BigOperators TensorProduct

namespace OddOrder.Higman.Suzuki2Groups

open Module
open OddOrder.RepresentationTheory

universe u uK uL uV uW

/-! ## Excluding gaps of length one and two -/

/-- A nonzero selected value of the actual alternating bracket cannot have
zero cyclic gap. -/
theorem gap_ne_zero_of_alternating
    {V W : Type u} [AddCommGroup V] [AddCommGroup W]
    {L : Type u} [Field L] [Module L V] [Module L W]
    {m : ℕ} [NeZero m]
    (b : Basis (Fin m) L V)
    (beta : LinearMap.BilinMap L V W)
    (hself : ∀ v, beta v v = 0)
    (r : Fin m)
    (hbracket : beta (b 0) (b r) ≠ 0) :
    r ≠ 0 := by
  intro hr
  subst r
  exact hbracket (hself (b 0))

private theorem exponent_dvd_of_two_pow_sub_one_dvd
    {a b : ℕ} (h : 2 ^ a - 1 ∣ 2 ^ b - 1) : a ∣ b := by
  have hgcd : 2 ^ Nat.gcd a b - 1 = 2 ^ a - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_eq_left h]
  have hpow : 2 ^ Nat.gcd a b = 2 ^ a := by
    have hpos₁ : 0 < 2 ^ Nat.gcd a b := by positivity
    have hpos₂ : 0 < 2 ^ a := by positivity
    omega
  have : Nat.gcd a b = a :=
    Nat.pow_right_injective (by omega) hpow
  exact (Nat.gcd_eq_left_iff_dvd).mp this

/-- Higman's exclusion of `m = 2r`, phrased as nonvanishing of the doubled
cyclic gap.  The only degree input is that `m = n*d` with `d` odd. -/
theorem twice_gap_ne_zero_of_odd_degree
    {L : Type u} [Field L] [Finite L] [Algebra (ZMod 2) L]
    {m n d : ℕ} [NeZero m]
    (hfin : finrank (ZMod 2) L = m)
    (hn : 0 < n)
    (hdegree : m = n * d)
    (hodd : Odd d)
    (lambda nu : L)
    (hprim : IsPrimitiveRoot nu (2 ^ n - 1))
    (r : Fin m) (hr : r ≠ 0)
    (hnu : nu = lambda ^ (1 + 2 ^ r.val)) :
    r + r ≠ 0 := by
  intro hrr
  have hrval : 0 < r.val := by
    apply Nat.pos_of_ne_zero
    intro hrval
    apply hr
    apply Fin.ext
    simpa using hrval
  have hval := congrArg Fin.val hrr
  have hm : m = r.val + r.val := by
    rw [Fin.val_add_eq_ite] at hval
    simp only [Fin.val_zero] at hval
    by_cases hwrap : m ≤ r.val + r.val
    · rw [if_pos hwrap] at hval
      omega
    · rw [if_neg hwrap] at hval
      omega
  letI : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card L = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2), hfin]
    norm_num [Nat.card_eq_fintype_card]
  have hlambdaCard : lambda ^ (2 ^ m) = lambda := by
    rw [← hcard]
    exact FiniteField.pow_card lambda
  have hfix : nu ^ (2 ^ r.val) = nu := by
    calc
      nu ^ (2 ^ r.val) =
          (lambda ^ (1 + 2 ^ r.val)) ^ (2 ^ r.val) := by rw [hnu]
      _ = lambda ^ ((1 + 2 ^ r.val) * 2 ^ r.val) := by rw [pow_mul]
      _ = lambda ^ (2 ^ r.val + 2 ^ (r.val + r.val)) := by
        congr 1
        rw [add_mul, one_mul, ← pow_add]
      _ = lambda ^ (2 ^ r.val + 2 ^ m) := by rw [← hm]
      _ = lambda ^ (2 ^ r.val) * lambda ^ (2 ^ m) := by rw [pow_add]
      _ = lambda ^ (2 ^ r.val) * lambda := by rw [hlambdaCard]
      _ = lambda * lambda ^ (2 ^ r.val) := mul_comm _ _
      _ = lambda ^ (1 + 2 ^ r.val) := by rw [pow_add, pow_one]
      _ = nu := hnu.symm
  have horderPos : 0 < 2 ^ n - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' (by omega))
  have hnuNe : nu ≠ 0 := (hprim.isUnit horderPos.ne').ne_zero
  have hpow : nu ^ (2 ^ r.val - 1) = 1 := by
    apply mul_left_cancel₀ hnuNe
    calc
      nu * nu ^ (2 ^ r.val - 1) =
          nu ^ (1 + (2 ^ r.val - 1)) := by rw [pow_add, pow_one]
      _ = nu ^ (2 ^ r.val) := by
        congr 1
        have : 0 < 2 ^ r.val := by positivity
        omega
      _ = nu := hfix
      _ = nu * 1 := (mul_one nu).symm
  have hpowDvd : 2 ^ n - 1 ∣ 2 ^ r.val - 1 := by
    rw [hprim.eq_orderOf]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hnDvdR : n ∣ r.val :=
    exponent_dvd_of_two_pow_sub_one_dvd hpowDvd
  obtain ⟨k, hk⟩ := hnDvdR
  have hmul : n * d = n * (2 * k) := by
    calc
      n * d = m := hdegree.symm
      _ = 2 * r.val := by omega
      _ = 2 * (n * k) := by rw [hk]
      _ = n * (2 * k) := by ac_rfl
  have hd : d = 2 * k := Nat.mul_left_cancel hn hmul
  exact (Nat.not_even_iff_odd.mpr hodd) (hd ▸ even_two_mul k)

/-! ## Collapsing the square sum to a relative trace -/

private def orderedEdge {alpha : Type*} [LinearOrder alpha]
    (tau : Equiv.Perm alpha) (i : alpha) : alpha × alpha :=
  if i < tau i then (i, tau i) else (tau i, i)

private def supportedUpperEdges {alpha : Type*} [Fintype alpha]
    [LinearOrder alpha] (tau : Equiv.Perm alpha) : Finset (alpha × alpha) :=
  (Finset.univ.product Finset.univ).filter fun p =>
    p.1 < p.2 ∧ (p.2 = tau p.1 ∨ p.1 = tau p.2)

/-- An upper-triangular sum supported on the undirected edges of a
permutation is its directed-edge sum, provided the permutation has no cycles
of length one or two. -/
private theorem sum_upperTriangle_eq_sum_permEdges
    {alpha A : Type*} [Fintype alpha] [LinearOrder alpha] [AddCommMonoid A]
    (tau : Equiv.Perm alpha)
    (hfix : ∀ i, tau i ≠ i)
    (htwo : ∀ i, tau (tau i) ≠ i)
    (F : alpha → alpha → A)
    (hsymm : ∀ i j, F i j = F j i)
    (hsupp : ∀ i j, j ≠ tau i → i ≠ tau j → F i j = 0) :
    (∑ i, ∑ j with i < j, F i j) = ∑ i, F i (tau i) := by
  let E := supportedUpperEdges tau
  let U := (Finset.univ.product Finset.univ).filter fun p : alpha × alpha =>
    p.1 < p.2
  have hedge_mem : ∀ i ∈ (Finset.univ : Finset alpha),
      orderedEdge tau i ∈ E := by
    intro i _hi
    simp only [E, supportedUpperEdges, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    by_cases hit : i < tau i
    · simp [orderedEdge, hit]
    · have hti : tau i < i :=
        lt_of_le_of_ne (le_of_not_gt hit) (hfix i)
      simp [orderedEdge, hit, hti]
  have hedge_inj : ∀ i ∈ (Finset.univ : Finset alpha),
      ∀ j ∈ Finset.univ, orderedEdge tau i = orderedEdge tau j → i = j := by
    intro i _hi j _hj hij
    by_cases hit : i < tau i <;> by_cases hjt : j < tau j
    · simpa [orderedEdge, hit, hjt] using congrArg Prod.fst hij
    · have hfirst : i = tau j := by
        simpa [orderedEdge, hit, hjt] using congrArg Prod.fst hij
      have hsecond : tau i = j := by
        simpa [orderedEdge, hit, hjt] using congrArg Prod.snd hij
      exfalso
      apply htwo j
      calc
        tau (tau j) = tau i := congrArg tau hfirst.symm
        _ = j := hsecond
    · have hfirst : tau i = j := by
        simpa [orderedEdge, hit, hjt] using congrArg Prod.fst hij
      have hsecond : i = tau j := by
        simpa [orderedEdge, hit, hjt] using congrArg Prod.snd hij
      exfalso
      apply htwo i
      calc
        tau (tau i) = tau j := congrArg tau hfirst
        _ = i := hsecond.symm
    · simpa [orderedEdge, hit, hjt] using congrArg Prod.snd hij
  have hedge_surj : ∀ p ∈ E, ∃ i, ∃ _ : i ∈ (Finset.univ : Finset alpha),
      orderedEdge tau i = p := by
    rintro ⟨a, b⟩ hp
    simp only [E, supportedUpperEdges, Finset.mem_filter] at hp
    rcases hp with ⟨_, hab, hsupport⟩
    rcases hsupport with hba | hab'
    · refine ⟨a, Finset.mem_univ _, ?_⟩
      simp [orderedEdge, hba ▸ hab, hba]
    · refine ⟨b, Finset.mem_univ _, ?_⟩
      have hnot : ¬ b < tau b := by
        simpa [hab'] using (not_lt_of_ge (le_of_lt hab))
      simp [orderedEdge, hnot, hab']
  have hedge_term : ∀ i ∈ (Finset.univ : Finset alpha),
      F i (tau i) = F (orderedEdge tau i).1 (orderedEdge tau i).2 := by
    intro i _hi
    by_cases hit : i < tau i
    · simp [orderedEdge, hit]
    · simpa [orderedEdge, hit] using hsymm i (tau i)
  have hdirected : (∑ i, F i (tau i)) =
      (∑ p ∈ E, F p.1 p.2) := by
    exact Finset.sum_bij (fun i _ => orderedEdge tau i) hedge_mem hedge_inj
      hedge_surj hedge_term
  have hEU : E ⊆ U := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpProd, hpLt, _⟩
    exact Finset.mem_filter.mpr ⟨hpProd, hpLt⟩
  have hzero : ∀ p ∈ U, p ∉ E → F p.1 p.2 = 0 := by
    intro p hpU hpE
    rcases Finset.mem_filter.mp hpU with ⟨hpProd, hpLt⟩
    apply hsupp
    · intro heq
      apply hpE
      exact Finset.mem_filter.mpr ⟨hpProd, hpLt, Or.inl heq⟩
    · intro heq
      apply hpE
      exact Finset.mem_filter.mpr ⟨hpProd, hpLt, Or.inr heq⟩
  have hEU_sum : (∑ p ∈ E, F p.1 p.2) =
      (∑ p ∈ U, F p.1 p.2) := Finset.sum_subset hEU hzero
  have hflatten : (∑ i, ∑ j with i < j, F i j) =
      (∑ p ∈ U, F p.1 p.2) := by
    simp only [U, Finset.sum_filter]
    convert (Finset.sum_product (Finset.univ : Finset alpha) Finset.univ
      (fun p : alpha × alpha => if p.1 < p.2 then F p.1 p.2 else 0)).symm
    congr 1
  exact (hflatten.trans hEU_sum.symm).trans hdirected.symm

/-- Reduction of a natural index modulo the absolute first-layer degree. -/
def higmanCyclicIndex {m : Nat} (hm : 0 < m) (k : Nat) : Fin m :=
  ⟨k % m, Nat.mod_lt _ hm⟩

/-- Cyclic successor on the Frobenius coordinates of a fixed degree. -/
def higmanCyclicSucc {m : Nat} (hm : 0 < m) (i : Fin m) : Fin m :=
  higmanCyclicIndex hm (i.val + 1)

private theorem higmanCyclicSucc_eq_add_one {m : Nat} [NeZero m]
    (hm : 0 < m) (i : Fin m) :
    higmanCyclicSucc hm i = i + 1 := by
  apply Fin.ext
  simp [higmanCyclicSucc, higmanCyclicIndex, Fin.val_add]

private theorem higmanCyclicIndex_succ {m : Nat} (hm : 0 < m) (k : Nat) :
    higmanCyclicSucc hm (higmanCyclicIndex hm k) = higmanCyclicIndex hm (k + 1) := by
  apply Fin.ext
  simp [higmanCyclicSucc, higmanCyclicIndex, Nat.add_mod]

private theorem higmanCyclicIndex_of_lt {m k : Nat} (hm : 0 < m) (hk : k < m) :
    higmanCyclicIndex hm k = ⟨k, hk⟩ := by
  apply Fin.ext
  simp [higmanCyclicIndex, Nat.mod_eq_of_lt hk]

private theorem higmanCyclicIndex_add {m : Nat} (hm : 0 < m) (i r : Fin m) :
    higmanCyclicIndex hm (i.val + r.val) = i + r := by
  apply Fin.ext
  simp [higmanCyclicIndex, Fin.val_add]

/-- Frobenius exponents respect cyclic addition modulo the absolute degree
of a finite characteristic-two field. -/
private theorem pow_two_cyclicAdd
    {L : Type uL} [Field L] [Finite L] [Algebra (ZMod 2) L]
    {m : Nat} (hfinL : Module.finrank (ZMod 2) L = m)
    (x : L) (i r : Fin m) :
    x ^ (2 ^ (i + r).val) =
      (x ^ (2 ^ r.val)) ^ (2 ^ i.val) := by
  let sigma := FiniteField.frobeniusAlgHom (ZMod 2) L
  have horder : orderOf sigma = m :=
    (FiniteField.orderOf_frobeniusAlgHom (ZMod 2) L).trans hfinL
  have hsigmaPow : sigma ^ m = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one sigma
  have hmod : Nat.ModEq m (i + r).val (r.val + i.val) := by
    change Nat.ModEq m ((i.val + r.val) % m) (r.val + i.val)
    simpa [add_comm] using Nat.mod_modEq (i.val + r.val) m
  have happ := DFunLike.congr_fun
    (pow_eq_pow_of_modEq hmod hsigmaPow) x
  have hraw : x ^ (2 ^ (i + r).val) =
      x ^ (2 ^ (r.val + i.val)) := by
    simpa only [sigma, AlgHom.coe_pow,
      FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card,
      AlgHom.one_apply] using happ
  calc
    x ^ (2 ^ (i + r).val) = x ^ (2 ^ (r.val + i.val)) := hraw
    _ = x ^ (2 ^ r.val * 2 ^ i.val) := by rw [pow_add]
    _ = (x ^ (2 ^ r.val)) ^ (2 ^ i.val) := pow_mul x _ _

/-- The tracked `HasHigmanPairGap` support predicate is exactly support on
the two orientations of the cyclic edge `r`. -/
theorem pairGap_imp_cyclicEdge
    {m : Nat} [NeZero m] (r i j : Fin m)
    (hgap : HasHigmanPairGap (ZMod.finEquiv m r) i j) :
    j = i + r ∨ i = j + r := by
  rcases hgap with hgap | hgap
  · left
    apply (ZMod.finEquiv m).injective
    rw [map_add]
    change ZMod.finEquiv m j - ZMod.finEquiv m i =
      ZMod.finEquiv m r at hgap
    calc
      ZMod.finEquiv m j =
          (ZMod.finEquiv m j - ZMod.finEquiv m i) +
            ZMod.finEquiv m i := by ring
      _ = ZMod.finEquiv m r + ZMod.finEquiv m i := by rw [hgap]
      _ = ZMod.finEquiv m i + ZMod.finEquiv m r := add_comm _ _
  · right
    apply (ZMod.finEquiv m).injective
    rw [map_add]
    change ZMod.finEquiv m j - ZMod.finEquiv m i =
      -ZMod.finEquiv m r at hgap
    calc
      ZMod.finEquiv m i =
          -(ZMod.finEquiv m j - ZMod.finEquiv m i) +
            ZMod.finEquiv m j := by ring
      _ = -(-ZMod.finEquiv m r) + ZMod.finEquiv m j := by rw [hgap]
      _ = ZMod.finEquiv m j + ZMod.finEquiv m r := by ring

/-- Contrapositive form used by the cyclic-edge sum collapse. -/
theorem eq_zero_of_pairGapSupport
    {m : Nat} [NeZero m] {A : Type*} [Zero A]
    (r : Fin m) (F : Fin m → Fin m → A)
    (hsupport : ∀ i j, F i j ≠ 0 →
      HasHigmanPairGap (ZMod.finEquiv m r) i j)
    (i j : Fin m) (hj : j ≠ i + r) (hi : i ≠ j + r) :
    F i j = 0 := by
  by_contra hne
  rcases pairGap_imp_cyclicEdge r i j (hsupport i j hne) with h | h
  · exact hj h
  · exact hi h

/-- The strongest purely algebraic part of Higman's Lemma 11 square
calculation. A single normalized edge coefficient, Frobenius cycling of both
bases, and single-gap support turn the Lemma 5 double sum into the relative
trace normal form consumed by Lemma 10. -/
theorem square_frobeniusSum_eq_trace_of_normalized_singleGap
    {K : Type uK} {L : Type uL} {V : Type uV} {W : Type uW}
    [Field K] [Field L] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [Algebra (ZMod 2) L]
    [AddCommMonoid V] [Module (ZMod 2) V]
    [AddCommMonoid W] [Module (ZMod 2) W]
    (B : LinearMap.BilinMap (ZMod 2) V W)
    (n d : Nat) [NeZero n] [NeZero (d * n)]
    (hn : 0 < n) (hd : 0 < d)
    (hcardK : Nat.card K = 2 ^ n)
    (hfinKL : Module.finrank K L = d)
    (hfinL : Module.finrank (ZMod 2) L = d * n)
    (bOne : Fin (d * n) → L ⊗[ZMod 2] V)
    (bTwo : Fin n → L ⊗[ZMod 2] W)
    (hcycleOne : ∀ i,
      frobeniusScalarBaseChange L (bOne i) =
        bOne (higmanCyclicSucc (Nat.mul_pos hd hn) i))
    (hcycleTwo : ∀ i,
      frobeniusScalarBaseChange L (bTwo i) = bTwo (higmanCyclicSucc hn i))
    (r : Fin (d * n)) (hr0 : r ≠ 0) (hrtwo : r + r ≠ 0)
    (epsilon : L)
    (hseed : B.baseChange L (bOne 0) (bOne r) = epsilon • bTwo 0)
    (hsymm : ∀ i j,
      B.baseChange L (bOne i) (bOne j) =
        B.baseChange L (bOne j) (bOne i))
    (hsupport : ∀ i j,
      j ≠ i + r → i ≠ j + r →
        B.baseChange L (bOne i) (bOne j) = 0)
    (alpha : L) :
    (∑ i : Fin (d * n), ∑ j : Fin (d * n) with i < j,
      alpha ^ (2 ^ i.val + 2 ^ j.val) •
        B.baseChange L (bOne i) (bOne j)) =
      ∑ s : Fin n,
        (algebraMap K L
          (Algebra.trace K L
            (alpha * alpha ^ (2 ^ r.val) * epsilon))) ^ (2 ^ s.val) •
          bTwo s := by
  let m := d * n
  have hm : 0 < m := Nat.mul_pos hd hn
  let u : Nat → L ⊗[ZMod 2] V := fun k => bOne (higmanCyclicIndex hm k)
  let v : Nat → L ⊗[ZMod 2] W := fun k => bTwo (higmanCyclicIndex hn k)
  have hu : ∀ k, frobeniusScalarBaseChange L (u k) = u (k + 1) := by
    intro k
    change frobeniusScalarBaseChange L (bOne (higmanCyclicIndex hm k)) =
      bOne (higmanCyclicIndex hm (k + 1))
    rw [hcycleOne]
    exact congrArg bOne (higmanCyclicIndex_succ hm k)
  have hv : ∀ k, frobeniusScalarBaseChange L (v k) = v (k + 1) := by
    intro k
    change frobeniusScalarBaseChange L (bTwo (higmanCyclicIndex hn k)) =
      bTwo (higmanCyclicIndex hn (k + 1))
    rw [hcycleTwo]
    exact congrArg bTwo (higmanCyclicIndex_succ hn k)
  have hseed' : B.baseChange L (u 0) (u r.val) = epsilon • v 0 := by
    have hzeroM : higmanCyclicIndex hm 0 = (0 : Fin m) := by
      apply Fin.ext
      simp [higmanCyclicIndex]
    have hrM : higmanCyclicIndex hm r.val = r := by
      apply Fin.ext
      change r.val % m = r.val
      exact Nat.mod_eq_of_lt r.isLt
    have hzeroN : higmanCyclicIndex hn 0 = (0 : Fin n) := by
      apply Fin.ext
      simp [higmanCyclicIndex]
    simpa only [u, v, hzeroM, hrM, hzeroN] using hseed
  have horbitNat := frobeniusScalarBaseChange_bilinear_orbit_formula
    B u v hu hv r.val epsilon hseed'
  have hedge (i : Fin m) :
      B.baseChange L (bOne i) (bOne (i + r)) =
        epsilon ^ (2 ^ i.val) •
          bTwo ⟨i.val % n, Nat.mod_lt _ hn⟩ := by
    have h := horbitNat i.val
    have hui : u i.val = bOne i := by
      change bOne (higmanCyclicIndex hm i.val) = bOne i
      rw [higmanCyclicIndex_of_lt hm i.isLt]
    have huir : u (i.val + r.val) = bOne (i + r) := by
      change bOne (higmanCyclicIndex hm (i.val + r.val)) = bOne (i + r)
      rw [higmanCyclicIndex_add hm i r]
    have hvi : v i.val = bTwo ⟨i.val % n, Nat.mod_lt _ hn⟩ := rfl
    simpa only [hui, huir, hvi] using h
  let tau : Equiv.Perm (Fin m) := Equiv.addRight r
  have hfix : ∀ i, tau i ≠ i := by
    intro i hEq
    apply hr0
    have hcancel : i + r = i + 0 := by simpa [tau] using hEq
    exact add_left_cancel hcancel
  have htwo : ∀ i, tau (tau i) ≠ i := by
    intro i hEq
    apply hrtwo
    have hcancel : i + (r + r) = i + 0 := by
      simpa [tau, add_assoc] using hEq
    exact add_left_cancel hcancel
  have hcollapse := sum_upperTriangle_eq_sum_permEdges tau hfix htwo
    (fun i j : Fin m =>
      alpha ^ (2 ^ i.val + 2 ^ j.val) •
        B.baseChange L (bOne i) (bOne j))
    (fun i j => by
      rw [hsymm, add_comm (2 ^ i.val) (2 ^ j.val)])
    (fun i j hj hi => by
      rw [hsupport i j (by simpa [tau] using hj)
        (by simpa [tau] using hi), smul_zero])
  calc
    (∑ i : Fin m, ∑ j : Fin m with i < j,
        alpha ^ (2 ^ i.val + 2 ^ j.val) •
          B.baseChange L (bOne i) (bOne j)) =
        ∑ i : Fin m,
          alpha ^ (2 ^ i.val + 2 ^ (i + r).val) •
            B.baseChange L (bOne i) (bOne (i + r)) := by
              simpa [tau] using hcollapse
    _ = ∑ i : Fin m,
        (alpha * alpha ^ (2 ^ r.val) * epsilon) ^ (2 ^ i.val) •
          bTwo ⟨i.val % n, Nat.mod_lt _ hn⟩ := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hedge, smul_smul]
      congr 1
      rw [pow_add, pow_two_cyclicAdd hfinL alpha i r]
      simp only [mul_pow]
    _ = ∑ s : Fin n,
        (algebraMap K L
          (Algebra.trace K L
            (alpha * alpha ^ (2 ^ r.val) * epsilon))) ^ (2 ^ s.val) •
          bTwo s :=
      trace_frobenius_coordinate_sum n d hn hcardK hfinKL
        (alpha * alpha ^ (2 ^ r.val) * epsilon) bTwo

/-- Descent of `square_frobeniusSum_eq_trace_of_normalized_singleGap` to the
ground second layer. This is the exact additive trace formula required by
Higman's Lemma 10. -/
theorem squareMap_eq_trace_of_normalized_singleGap
    {K : Type uK} {L : Type uL} {V : Type uV} {W : Type uW}
    [Field K] [Field L] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [Algebra (ZMod 2) L]
    [AddCommMonoid V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (B : LinearMap.BilinMap (ZMod 2) V W)
    (n d : Nat) [NeZero n] [NeZero (d * n)]
    (hn : 0 < n) (hd : 0 < d)
    (hcardK : Nat.card K = 2 ^ n)
    (hfinKL : Module.finrank K L = d)
    (hfinL : Module.finrank (ZMod 2) L = d * n)
    (bOne : Fin (d * n) → L ⊗[ZMod 2] V)
    (bTwo : Fin n → L ⊗[ZMod 2] W)
    (hcycleOne : ∀ i,
      frobeniusScalarBaseChange L (bOne i) =
        bOne (higmanCyclicSucc (Nat.mul_pos hd hn) i))
    (hcycleTwo : ∀ i,
      frobeniusScalarBaseChange L (bTwo i) = bTwo (higmanCyclicSucc hn i))
    (r : Fin (d * n)) (hr0 : r ≠ 0) (hrtwo : r + r ≠ 0)
    (epsilon : L)
    (hseed : B.baseChange L (bOne 0) (bOne r) = epsilon • bTwo 0)
    (hsymm : ∀ i j,
      B.baseChange L (bOne i) (bOne j) =
        B.baseChange L (bOne j) (bOne i))
    (hsupport : ∀ i j,
      j ≠ i + r → i ≠ j + r →
        B.baseChange L (bOne i) (bOne j) = 0)
    (q : L → W) (iotaAdd : K →+ W)
    (hTwoExpansion : ∀ z : K,
      (1 : L) ⊗ₜ[ZMod 2] iotaAdd z =
        ∑ s : Fin n, (algebraMap K L z) ^ (2 ^ s.val) • bTwo s)
    (alpha : L)
    (hq : (1 : L) ⊗ₜ[ZMod 2] q alpha =
      ∑ i : Fin (d * n), ∑ j : Fin (d * n) with i < j,
        alpha ^ (2 ^ i.val + 2 ^ j.val) •
          B.baseChange L (bOne i) (bOne j)) :
    q alpha = iotaAdd
      (Algebra.trace K L
        (alpha * alpha ^ (2 ^ r.val) * epsilon)) := by
  let z := Algebra.trace K L
    (alpha * alpha ^ (2 ^ r.val) * epsilon)
  have htrace := square_frobeniusSum_eq_trace_of_normalized_singleGap
    B n d hn hd hcardK hfinKL hfinL bOne bTwo hcycleOne hcycleTwo
    r hr0 hrtwo epsilon hseed hsymm hsupport alpha
  have htensor : (1 : L) ⊗ₜ[ZMod 2] q alpha =
      (1 : L) ⊗ₜ[ZMod 2] iotaAdd z := by
    calc
      (1 : L) ⊗ₜ[ZMod 2] q alpha =
          ∑ i : Fin (d * n), ∑ j : Fin (d * n) with i < j,
            alpha ^ (2 ^ i.val + 2 ^ j.val) •
              B.baseChange L (bOne i) (bOne j) := hq
      _ = ∑ s : Fin n,
          (algebraMap K L z) ^ (2 ^ s.val) • bTwo s := htrace
      _ = (1 : L) ⊗ₜ[ZMod 2] iotaAdd z := (hTwoExpansion z).symm
  apply sub_eq_zero.mp
  apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff
    (R := ZMod 2) (M := W) (A := L) (q alpha - iotaAdd z)).mp
  calc
    (1 : L) ⊗ₜ[ZMod 2] (q alpha - iotaAdd z) =
        (1 : L) ⊗ₜ[ZMod 2] q alpha -
          (1 : L) ⊗ₜ[ZMod 2] iotaAdd z := by
            rw [TensorProduct.tmul_sub]
    _ = 0 := sub_eq_zero.mpr htensor

/-- Anchor-general form of the trace calculation.  It consumes the original
Lemma 5 basis directly: the chosen nonzero bracket may occur at `(a,a+r)`
and on the `s₀`-th second-layer eigenline.  Thus normalizing by Frobenius
rotation does not require transporting the square formula itself. -/
theorem square_frobeniusSum_eq_trace_of_anchored_singleGap
    {K : Type uK} {L : Type uL} {V : Type uV} {W : Type uW}
    [Field K] [Field L] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [Algebra (ZMod 2) L]
    [AddCommMonoid V] [Module (ZMod 2) V]
    [AddCommMonoid W] [Module (ZMod 2) W]
    (B : LinearMap.BilinMap (ZMod 2) V W)
    (n d : Nat) [NeZero n] [NeZero (d * n)]
    (hn : 0 < n) (hd : 0 < d)
    (hcardK : Nat.card K = 2 ^ n)
    (hfinKL : Module.finrank K L = d)
    (hfinL : Module.finrank (ZMod 2) L = d * n)
    (bOne : Fin (d * n) → L ⊗[ZMod 2] V)
    (bTwo : Fin n → L ⊗[ZMod 2] W)
    (hcycleOne : ∀ i,
      frobeniusScalarBaseChange L (bOne i) =
        bOne (higmanCyclicSucc (Nat.mul_pos hd hn) i))
    (hcycleTwo : ∀ i,
      frobeniusScalarBaseChange L (bTwo i) = bTwo (higmanCyclicSucc hn i))
    (a : Fin (d * n)) (s₀ : Fin n)
    (r : Fin (d * n)) (hr0 : r ≠ 0) (hrtwo : r + r ≠ 0)
    (epsilon : L)
    (hseed : B.baseChange L (bOne a) (bOne (a + r)) =
      epsilon • bTwo s₀)
    (hsymm : ∀ i j,
      B.baseChange L (bOne i) (bOne j) =
        B.baseChange L (bOne j) (bOne i))
    (hsupport : ∀ i j,
      j ≠ i + r → i ≠ j + r →
        B.baseChange L (bOne i) (bOne j) = 0)
    (alpha : L) :
    (∑ i : Fin (d * n), ∑ j : Fin (d * n) with i < j,
      alpha ^ (2 ^ i.val + 2 ^ j.val) •
        B.baseChange L (bOne i) (bOne j)) =
      ∑ s : Fin n,
        (algebraMap K L
          (Algebra.trace K L
            (alpha ^ (2 ^ a.val) *
              (alpha ^ (2 ^ a.val)) ^ (2 ^ r.val) * epsilon))) ^
            (2 ^ s.val) • bTwo (s₀ + s) := by
  let m := d * n
  have hm : 0 < m := Nat.mul_pos hd hn
  let u : Nat → L ⊗[ZMod 2] V := fun k =>
    bOne (a + higmanCyclicIndex hm k)
  let v : Nat → L ⊗[ZMod 2] W := fun k =>
    bTwo (s₀ + higmanCyclicIndex hn k)
  have hu : ∀ k, frobeniusScalarBaseChange L (u k) = u (k + 1) := by
    intro k
    change frobeniusScalarBaseChange L
      (bOne (a + higmanCyclicIndex hm k)) =
        bOne (a + higmanCyclicIndex hm (k + 1))
    rw [hcycleOne, higmanCyclicSucc_eq_add_one, add_assoc,
      ← higmanCyclicSucc_eq_add_one, higmanCyclicIndex_succ]
  have hv : ∀ k, frobeniusScalarBaseChange L (v k) = v (k + 1) := by
    intro k
    change frobeniusScalarBaseChange L
      (bTwo (s₀ + higmanCyclicIndex hn k)) =
        bTwo (s₀ + higmanCyclicIndex hn (k + 1))
    rw [hcycleTwo, higmanCyclicSucc_eq_add_one, add_assoc,
      ← higmanCyclicSucc_eq_add_one, higmanCyclicIndex_succ]
  have hseed' : B.baseChange L (u 0) (u r.val) = epsilon • v 0 := by
    have hzeroM : higmanCyclicIndex hm 0 = (0 : Fin m) := by
      apply Fin.ext
      simp [higmanCyclicIndex]
    have hrM : higmanCyclicIndex hm r.val = r := by
      apply Fin.ext
      change r.val % m = r.val
      exact Nat.mod_eq_of_lt r.isLt
    have hzeroN : higmanCyclicIndex hn 0 = (0 : Fin n) := by
      apply Fin.ext
      simp [higmanCyclicIndex]
    simpa only [u, v, hzeroM, hrM, hzeroN, add_zero] using hseed
  have horbitNat := frobeniusScalarBaseChange_bilinear_orbit_formula
    B u v hu hv r.val epsilon hseed'
  have hedge (k : Fin m) :
      B.baseChange L (bOne (a + k)) (bOne (a + k + r)) =
        epsilon ^ (2 ^ k.val) •
          bTwo (s₀ + ⟨k.val % n, Nat.mod_lt _ hn⟩) := by
    have h := horbitNat k.val
    have huk : u k.val = bOne (a + k) := by
      change bOne (a + higmanCyclicIndex hm k.val) = bOne (a + k)
      rw [higmanCyclicIndex_of_lt hm k.isLt]
    have hukr : u (k.val + r.val) = bOne (a + k + r) := by
      change bOne (a + higmanCyclicIndex hm (k.val + r.val)) =
        bOne (a + k + r)
      rw [higmanCyclicIndex_add hm k r, add_assoc]
    have hvk : v k.val =
        bTwo (s₀ + ⟨k.val % n, Nat.mod_lt _ hn⟩) := by
      rfl
    simpa only [huk, hukr, hvk] using h
  let tau : Equiv.Perm (Fin m) := Equiv.addRight r
  have hfix : ∀ i, tau i ≠ i := by
    intro i hEq
    apply hr0
    have hcancel : i + r = i + 0 := by simpa [tau] using hEq
    exact add_left_cancel hcancel
  have htwo : ∀ i, tau (tau i) ≠ i := by
    intro i hEq
    apply hrtwo
    have hcancel : i + (r + r) = i + 0 := by
      simpa [tau, add_assoc] using hEq
    exact add_left_cancel hcancel
  have hcollapse := sum_upperTriangle_eq_sum_permEdges tau hfix htwo
    (fun i j : Fin m =>
      alpha ^ (2 ^ i.val + 2 ^ j.val) •
        B.baseChange L (bOne i) (bOne j))
    (fun i j => by
      rw [hsymm, add_comm (2 ^ i.val) (2 ^ j.val)])
    (fun i j hj hi => by
      rw [hsupport i j (by simpa [tau] using hj)
        (by simpa [tau] using hi), smul_zero])
  let alpha₀ := alpha ^ (2 ^ a.val)
  let z := alpha₀ * alpha₀ ^ (2 ^ r.val) * epsilon
  have hfirst (k : Fin m) :
      alpha ^ (2 ^ (a + k).val) = alpha₀ ^ (2 ^ k.val) := by
    simpa only [alpha₀, add_comm] using
      (pow_two_cyclicAdd hfinL alpha k a)
  have hsecond (k : Fin m) :
      alpha ^ (2 ^ (a + k + r).val) =
        (alpha₀ ^ (2 ^ r.val)) ^ (2 ^ k.val) := by
    calc
      alpha ^ (2 ^ (a + k + r).val) =
          alpha₀ ^ (2 ^ (k + r).val) := by
        simpa only [alpha₀, add_comm, add_left_comm, add_assoc] using
          (pow_two_cyclicAdd hfinL alpha (k + r) a)
      _ = (alpha₀ ^ (2 ^ r.val)) ^ (2 ^ k.val) :=
        pow_two_cyclicAdd hfinL alpha₀ k r
  calc
    (∑ i : Fin m, ∑ j : Fin m with i < j,
        alpha ^ (2 ^ i.val + 2 ^ j.val) •
          B.baseChange L (bOne i) (bOne j)) =
        ∑ i : Fin m,
          alpha ^ (2 ^ i.val + 2 ^ (i + r).val) •
            B.baseChange L (bOne i) (bOne (i + r)) := by
              simpa [tau] using hcollapse
    _ = ∑ k : Fin m,
          alpha ^ (2 ^ (a + k).val + 2 ^ (a + k + r).val) •
            B.baseChange L (bOne (a + k)) (bOne (a + k + r)) := by
      exact (Equiv.sum_comp (Equiv.addLeft a)
        (fun i : Fin m =>
          alpha ^ (2 ^ i.val + 2 ^ (i + r).val) •
            B.baseChange L (bOne i) (bOne (i + r)))).symm
    _ = ∑ k : Fin m, z ^ (2 ^ k.val) •
          bTwo (s₀ + ⟨k.val % n, Nat.mod_lt _ hn⟩) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [hedge, smul_smul, pow_add, hfirst, hsecond]
      simp only [z, mul_pow]
    _ = ∑ s : Fin n,
        (algebraMap K L (Algebra.trace K L z)) ^ (2 ^ s.val) •
          bTwo (s₀ + s) :=
      trace_frobenius_coordinate_sum n d hn hcardK hfinKL z
        (fun s => bTwo (s₀ + s))

/-- Ground-layer descent of the anchor-general trace calculation.  This lets
the Lemma 5 basis retain its original indexing while producing the exact
additive trace formula consumed by Higman's Lemma 10. -/
theorem squareMap_eq_trace_of_anchored_singleGap
    {K : Type uK} {L : Type uL} {V : Type uV} {W : Type uW}
    [Field K] [Field L] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    [Algebra (ZMod 2) L]
    [AddCommMonoid V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (B : LinearMap.BilinMap (ZMod 2) V W)
    (n d : Nat) [NeZero n] [NeZero (d * n)]
    (hn : 0 < n) (hd : 0 < d)
    (hcardK : Nat.card K = 2 ^ n)
    (hfinKL : Module.finrank K L = d)
    (hfinL : Module.finrank (ZMod 2) L = d * n)
    (bOne : Fin (d * n) → L ⊗[ZMod 2] V)
    (bTwo : Fin n → L ⊗[ZMod 2] W)
    (hcycleOne : ∀ i,
      frobeniusScalarBaseChange L (bOne i) =
        bOne (higmanCyclicSucc (Nat.mul_pos hd hn) i))
    (hcycleTwo : ∀ i,
      frobeniusScalarBaseChange L (bTwo i) =
        bTwo (higmanCyclicSucc hn i))
    (a : Fin (d * n)) (s₀ : Fin n)
    (r : Fin (d * n)) (hr0 : r ≠ 0) (hrtwo : r + r ≠ 0)
    (epsilon : L)
    (hseed : B.baseChange L (bOne a) (bOne (a + r)) =
      epsilon • bTwo s₀)
    (hsymm : ∀ i j,
      B.baseChange L (bOne i) (bOne j) =
        B.baseChange L (bOne j) (bOne i))
    (hsupport : ∀ i j,
      j ≠ i + r → i ≠ j + r →
        B.baseChange L (bOne i) (bOne j) = 0)
    (q : L → W) (iotaAdd : K →+ W)
    (hTwoExpansion : ∀ z : K,
      (1 : L) ⊗ₜ[ZMod 2] iotaAdd z =
        ∑ s : Fin n,
          (algebraMap K L z) ^ (2 ^ s.val) • bTwo (s₀ + s))
    (alpha : L)
    (hq : (1 : L) ⊗ₜ[ZMod 2] q alpha =
      ∑ i : Fin (d * n), ∑ j : Fin (d * n) with i < j,
        alpha ^ (2 ^ i.val + 2 ^ j.val) •
          B.baseChange L (bOne i) (bOne j)) :
    q alpha = iotaAdd
      (Algebra.trace K L
        (alpha ^ (2 ^ a.val) *
          (alpha ^ (2 ^ a.val)) ^ (2 ^ r.val) * epsilon)) := by
  let z := Algebra.trace K L
    (alpha ^ (2 ^ a.val) *
      (alpha ^ (2 ^ a.val)) ^ (2 ^ r.val) * epsilon)
  have htrace := square_frobeniusSum_eq_trace_of_anchored_singleGap
    B n d hn hd hcardK hfinKL hfinL bOne bTwo hcycleOne hcycleTwo
    a s₀ r hr0 hrtwo epsilon hseed hsymm hsupport alpha
  have htensor : (1 : L) ⊗ₜ[ZMod 2] q alpha =
      (1 : L) ⊗ₜ[ZMod 2] iotaAdd z := by
    calc
      (1 : L) ⊗ₜ[ZMod 2] q alpha =
          ∑ i : Fin (d * n), ∑ j : Fin (d * n) with i < j,
            alpha ^ (2 ^ i.val + 2 ^ j.val) •
              B.baseChange L (bOne i) (bOne j) := hq
      _ = ∑ s : Fin n,
          (algebraMap K L z) ^ (2 ^ s.val) • bTwo (s₀ + s) := htrace
      _ = (1 : L) ⊗ₜ[ZMod 2] iotaAdd z := (hTwoExpansion z).symm
  apply sub_eq_zero.mp
  apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff
    (R := ZMod 2) (M := W) (A := L) (q alpha - iotaAdd z)).mp
  calc
    (1 : L) ⊗ₜ[ZMod 2] (q alpha - iotaAdd z) =
        (1 : L) ⊗ₜ[ZMod 2] q alpha -
          (1 : L) ⊗ₜ[ZMod 2] iotaAdd z := by
            rw [TensorProduct.tmul_sub]
    _ = 0 := sub_eq_zero.mpr htensor

/-! ### Shifted ground coordinates for the second layer -/

/-- Frobenius exponents respect cyclic addition modulo the absolute degree
of a finite characteristic-two field. -/
private theorem pow_two_cyclicAdd_for_shiftedExpansion
    {K : Type uK} [Field K] [Finite K] [Algebra (ZMod 2) K]
    {n : Nat} (hfinK : Module.finrank (ZMod 2) K = n)
    (x : K) (i r : Fin n) :
    x ^ (2 ^ (i + r).val) =
      (x ^ (2 ^ r.val)) ^ (2 ^ i.val) := by
  let sigma := FiniteField.frobeniusAlgHom (ZMod 2) K
  have horder : orderOf sigma = n :=
    (FiniteField.orderOf_frobeniusAlgHom (ZMod 2) K).trans hfinK
  have hsigmaPow : sigma ^ n = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one sigma
  have hmod : Nat.ModEq n (i + r).val (r.val + i.val) := by
    change Nat.ModEq n ((i.val + r.val) % n) (r.val + i.val)
    simpa [add_comm] using Nat.mod_modEq (i.val + r.val) n
  have happ := DFunLike.congr_fun
    (pow_eq_pow_of_modEq hmod hsigmaPow) x
  have hraw : x ^ (2 ^ (i + r).val) =
      x ^ (2 ^ (r.val + i.val)) := by
    simpa only [sigma, AlgHom.coe_pow,
      FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card,
      AlgHom.one_apply] using happ
  calc
    x ^ (2 ^ (i + r).val) = x ^ (2 ^ (r.val + i.val)) := hraw
    _ = x ^ (2 ^ r.val * 2 ^ i.val) := by rw [pow_add]
    _ = (x ^ (2 ^ r.val)) ^ (2 ^ i.val) := pow_mul x _ _

/-- Shift a second-layer field model by the anchor Frobenius.  The inverse of
the shifted linear equivalence has the conjugate-basis expansion indexed from
that anchor. -/
theorem exists_shiftedSecondLinearEquiv_expansion
    {K : Type uK} {L : Type uL} {V : Type uV}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    [AddCommGroup V] [Module (ZMod 2) V]
    [NeZero (finrank (ZMod 2) K)]
    (iota : K →ₐ[ZMod 2] L) (eTwo : V ≃ₗ[ZMod 2] K)
    (s₀ : Fin (finrank (ZMod 2) K)) :
    letI : Algebra K L := iota.toRingHom.toAlgebra
    let n := finrank (ZMod 2) K
    let bTwo := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo
    ∃ eTwoShift : V ≃ₗ[ZMod 2] K, ∀ z : K,
      (1 : L) ⊗ₜ[ZMod 2] eTwoShift.symm z =
        ∑ s : Fin n,
          (algebraMap K L z) ^ (2 ^ s.val) • bTwo (s₀ + s) := by
  letI : Algebra K L := iota.toRingHom.toAlgebra
  let n := finrank (ZMod 2) K
  let bTwo := conjugateTensorBasisAlongOfLinearEquiv K L iota eTwo
  let sigma : K ≃ₐ[ZMod 2] K :=
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ s₀.val
  let eTwoShift : V ≃ₗ[ZMod 2] K :=
    eTwo.trans sigma.toLinearEquiv
  refine ⟨eTwoShift, ?_⟩
  intro z
  let w : K := sigma.symm z
  have hsigma_apply (x : K) : sigma x = x ^ (2 ^ s₀.val) := by
    simp [sigma, AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate]
  have hw : w ^ (2 ^ s₀.val) = z := by
    calc
      w ^ (2 ^ s₀.val) = sigma w := (hsigma_apply w).symm
      _ = z := by simpa only [w] using sigma.apply_symm_apply z
  have hpow (s : Fin n) :
      w ^ (2 ^ (s₀ + s).val) = z ^ (2 ^ s.val) := by
    rw [add_comm]
    rw [pow_two_cyclicAdd_for_shiftedExpansion
      (K := K) (n := n) rfl w s s₀, hw]
  have hexpand :=
    one_tmul_eq_sum_conjugateTensorBasisAlongOfLinearEquiv
      K L iota eTwo (eTwo.symm w)
  change (1 : L) ⊗ₜ[ZMod 2] eTwo.symm w = _
  calc
    (1 : L) ⊗ₜ[ZMod 2] eTwo.symm w =
        ∑ t : Fin n, iota (w ^ (2 ^ t.val)) • bTwo t := by
      simpa only [n, bTwo, eTwo.apply_symm_apply] using hexpand
    _ = ∑ s : Fin n,
        iota (w ^ (2 ^ (s₀ + s).val)) • bTwo (s₀ + s) := by
      simpa only [Equiv.coe_addLeft] using
        (Equiv.sum_comp (Equiv.addLeft s₀)
          (fun t : Fin n ↦
            iota (w ^ (2 ^ t.val)) • bTwo t)).symm
    _ = ∑ s : Fin n,
        (algebraMap K L z) ^ (2 ^ s.val) • bTwo (s₀ + s) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [hpow, map_pow]
      rfl

end OddOrder.Higman.Suzuki2Groups
