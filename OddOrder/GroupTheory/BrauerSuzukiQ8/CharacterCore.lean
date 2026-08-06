/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiQ8.Reduction
import OddOrder.GroupTheory.CentralInvolutionNormalComplement
import OddOrder.GroupTheory.RepresentationTheory.Modular.AnalysisAtInvolution
import OddOrder.GroupTheory.RepresentationTheory.Modular.BasicSetDegreeOdd
import OddOrder.GroupTheory.RepresentationTheory.Modular.InvolutionClassBurnside
import OddOrder.GroupTheory.RepresentationTheory.Modular.InvolutionColumnExpansion
import OddOrder.GroupTheory.RepresentationTheory.Modular.PadicComplexDatum
import OddOrder.GroupTheory.RepresentationTheory.Modular.ThirdMainConverseSupply

/-!
# Brauer–Suzuki, the `Q₈` case: the character-theoretic core (Navarro pp. 139–146)

`q8_exists_proper_normal` is the whole content of the `Q₈` branch: the involution of a proper
quaternion Sylow `2`-subgroup lies in a proper normal subgroup.  Navarro obtains it as the kernel
of a nontrivial character of the principal block, through the "analysis at `y`" and the "analysis
at `t`" of pp. 140–145.

The character-theoretic engine is `exists_proper_normal_of_columns`; every one of its hypotheses
has a supplier in `GroupTheory/RepresentationTheory/Modular/`, and this file is where they are
instantiated for the `Q₈` configuration (issue 9506).

## Main results

* `OddOrder.GroupTheory.q8_exists_proper_normal`
-/

open OddOrder.Isaacs.Ch03
open OddOrder.RepresentationTheory.Modular

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

set_option maxHeartbeats 3200000 in
-- Five modular data and the whole (7.2)/(7.4)/(7.6) chain are instantiated in one term.
/-- **Navarro pp. 139–146, the character-theoretic core** (issue 9506, `sorry`): when the
quaternion Sylow `2`-subgroup is proper, its involution lies in a proper normal subgroup.

This is Navarro's "our objective is to find a nontrivial character in the principal block of `G`
which contains `t` in its kernel" — the kernel of such a character is the proper normal subgroup.
The proof occupies the eight pages pp. 139–146: a unique `G`-class of elements of order `4`
(fusion control plus `Aut(Q₈) = Sym(4)`), then the "analysis at `y`" and "analysis at `t`" with
the principal-block basic set of Navarro (7.3)/(7.4), for which the integral change-of-basis
matrix `intBasicSetMatrix` (issue 9508, closed) is the prerequisite. -/
theorem q8_exists_proper_normal (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (e : ↥(T : Subgroup G) ≃* QuaternionGroup 2) (hTG : (T : Subgroup G) ≠ ⊤)
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ z ∈ N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype G := Fintype.ofFinite G
  -- the datum of `G` over `𝓞_ℂ_[2]`
  obtain ⟨ι'G, _, mG, _, _, _, eG, ιG, _, nnG, _, _, _, πG, hπG, hlinG, ωG, ω'G,
    hkerJG, hnilG, hωG, hω'G⟩ :=
    exists_datum_padicComplex 2 G
  -- the centraliser of the involution, and its datum
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  haveI : Finite ↥C := Subtype.finite
  obtain ⟨ι'C, _, mC, _, _, _, eC, ιC, _, nnC, _, _, _, πC, hπC, hlinC, ωC, ω'C,
    hkerJC, hnilC, hωC, hω'C⟩ :=
    exists_datum_padicComplex 2 ↥C
  -- the central subgroup `⟨z⟩ ⊴ C_G(z)` and the quotient `Q = C_G(z)/⟨z⟩`
  have hzC : z ∈ C := Subgroup.mem_centralizer_iff.mpr fun w hw => by
    rw [Set.mem_singleton_iff] at hw; subst hw; rfl
  set Nz : Subgroup ↥C := Subgroup.zpowers (⟨z, hzC⟩ : ↥C) with hNz
  haveI : Nz.Normal := zpowers_self_normal_centralizer z hzC
  have hNzcard : Nat.card ↥Nz = 2 := by
    rw [hNz, Nat.card_zpowers,
      ← orderOf_injective C.subtype (Subgroup.subtype_injective _) (⟨z, hzC⟩ : ↥C)]
    exact hz
  have hNzP : IsPGroup 2 ↥Nz := IsPGroup.of_card (n := 1) (by rw [hNzcard, pow_one])
  haveI : Finite (↥C ⧸ Nz) := Quotient.finite _
  -- the ordinary splitting of `Q`; its *modular* splitting must be `quotientPi` of that of `C`,
  -- so that `IBr(Q)` and `IBr(C)` share their index type (Navarro (7.6))
  obtain ⟨ι'Q, _, mQ, _, _, _, eQ, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    exists_datum_padicComplex 2 (↥C ⧸ Nz)
  obtain ⟨ϖ, hϖ⟩ :=
    exists_isPrimitiveRoot_pRegularExponent 2 (↥C ⧸ Nz)
  obtain ⟨ϖ', hϖ'⟩ :=
    exists_isPrimitiveRoot_residueField_pRegularExponent 2
      (↥C ⧸ Nz)
  have hkerJQ := ker_quotientPi πC hπC hlinC hNzP hkerJC
  have hnilQ := fun w hw =>
    OddOrder.GroupAlgebra.isNilpotent_of_blockCharacterPi_eq_zero
      (quotientPi πC hπC hlinC hNzP).toRingHom
      (quotientPi_surjective πC hπC hlinC hNzP)
      (quotientPi_smul πC hπC hlinC hNzP) hkerJQ w hw
  -- an involution `ȳ` of `Q`: its Sylow `2`-subgroups have order `4`
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  obtain ⟨SQ⟩ : Nonempty (Sylow 2 (↥C ⧸ Nz)) := Sylow.nonempty
  have hSQ4 : Nat.card ↥(SQ : Subgroup (↥C ⧸ Nz)) = 4 :=
    card_sylow_quotient_centralizer T e hzT hz2 hz1 hzC SQ
  haveI : Fintype ↥(SQ : Subgroup (↥C ⧸ Nz)) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ : ∃ u : ↥(SQ : Subgroup (↥C ⧸ Nz)), orderOf u = 2 := by
    refine exists_prime_orderOf_dvd_card 2 ?_
    rw [← Nat.card_eq_fintype_card, hSQ4]
    norm_num
  set yb : ↥C ⧸ Nz := (u : ↥C ⧸ Nz) with hyb
  have hyb1 : yb ≠ 1 := fun h => by
    have : orderOf u = 1 := by
      rw [← orderOf_injective (SQ : Subgroup (↥C ⧸ Nz)).subtype (Subgroup.subtype_injective _) u]
      simp [← hyb, h]
    rw [hu] at this; omega
  have hyb2 : yb * yb = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu, pow_two] at h
    rw [hyb, ← Subgroup.coe_mul, h, Subgroup.coe_one]
  -- `C_Q(ȳ)` has a normal `2`-complement (Navarro (7.2)) and its Sylow `2`-subgroup has order `4`
  have hcompl := hasNormalPComplement_centralizer_of_card_sylow_four SQ hSQ4 hyb1 hyb2
  obtain ⟨M, hMnorm, hMp, nM, hMindex⟩ := exists_normal_of_hasNormalPComplement hcompl
  obtain ⟨SylC⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({yb} : Set (↥C ⧸ Nz)))) :=
    Sylow.nonempty
  have hSylC4 : Nat.card ↥(SylC : Subgroup ↥(Subgroup.centralizer ({yb} : Set (↥C ⧸ Nz)))) = 4 :=
    card_sylow_centralizer_of_card_sylow_four SQ hSQ4 hyb1 hyb2 SylC
  -- the datum of `C_Q(ȳ)`, and the index of its principal block
  haveI : Finite ↥(Subgroup.centralizer ({yb} : Set (↥C ⧸ Nz))) := Subtype.finite
  obtain ⟨ι'Y, _, mY, _, _, _, eY, ιY, _, nnY, _, _, _, πY, hπY, hlinY, ωY, ω'Y,
    hkerJY, hnilY, hωY, hω'Y⟩ :=
    exists_datum_padicComplex 2
      ↥(Subgroup.centralizer ({yb} : Set (↥C ⧸ Nz)))
  obtain ⟨φ₀, hφ₀⟩ := Quotient.exists_rep
    (principalBlock πY hπY hlinY hnilY)
  -- Navarro (6.13): the Cartan invariant of the principal block of `C_Q(ȳ)` is `|Sylow| = 4`
  haveI : Fintype ↥(Subgroup.centralizer ({yb} : Set (↥C ⧸ Nz))) := Fintype.ofFinite _
  have hcart : cartanMatrix
      (𝒪 := 𝓞_ℂ_[2]) (nn := nnY) Nat.prime_two hωY hω'Y hπY hlinY hkerJY eY φ₀ φ₀ = 4 := by
    rw [cartanMatrix_principalBlock_eq_card_sylow_of_hasNormalPComplement Nat.prime_two hωY hω'Y
      hπY hlinY hkerJY hnilY eY hcompl SylC hφ₀, hSylC4]
  -- the `p`-th root of unity separating the `p`-part
  obtain ⟨ζ, hζ, hζk, hζK⟩ :=
    exists_pow_eq_one_residue_eq_one_padicComplexInt 2
  -- the converse of Brauer's third main theorem, for both pairs
  have hzP : IsPElement 2 z := ⟨1, by rw [hz, pow_one]⟩
  have hybP : IsPElement 2 yb := ⟨1, by
    rw [pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hyb2) hyb1⟩
  have hroot : ∀ n : ℕ, ¬ 2 ∣ n → n ≠ 0 → ∃ ζ' : 𝓞_ℂ_[2], IsPrimitiveRoot ζ' n :=
    fun n hn hn0 => exists_isPrimitiveRoot_padicComplexInt 2 hn hn0
  have hroot' : ∀ n : ℕ, ¬ 2 ∣ n → n ≠ 0 →
      ∃ ζ' : IsLocalRing.ResidueField 𝓞_ℂ_[2], IsPrimitiveRoot ζ' n :=
    fun n hn hn0 => exists_isPrimitiveRoot_residueField_padicComplexInt 2 hn hn0
  haveI : DecidableEq (ConjClasses G) := Classical.decEq _
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hconvG := fun b hind =>
    eq_principalBlock_of_inducedBlockOfCentralizer_eq_of_roots (K := ℂ_[2]) Nat.prime_two hzP
      hroot hroot' hζ hζk hζK eG eC hπG hlinG hnilG hkerJG hπC hlinC hnilC hkerJC b hind
  -- the centrality of `⟨z⟩` in `C_G(z)`, as the `p`-regular commutation the chain asks for
  have hcent : ∀ w : ↥C, IsPRegular 2 w → ∀ v ∈ Nz, Commute w v := fun w _ v hv =>
    Subgroup.mem_center_iff.mp (zpowers_self_le_center_centralizer z hzC hv) w
  -- the same converse, for the pair `(Q, C_Q(ȳ))`
  haveI : Fintype (↥C ⧸ Nz) := Fintype.ofFinite _
  haveI : DecidableEq (ConjClasses (↥C ⧸ Nz)) := Classical.decEq _
  haveI : Fintype (ConjClasses (↥C ⧸ Nz)) := Fintype.ofFinite _
  have hconvC := fun b hind =>
    eq_principalBlock_of_inducedBlockOfCentralizer_eq_of_roots (K := ℂ_[2]) Nat.prime_two hybP
      hroot hroot' hζ hζk hζK eQ eY (quotientPi_surjective πC hπC hlinC hNzP)
      (quotientPi_smul πC hπC hlinC hNzP) hnilQ hkerJQ hπY hlinY hnilY hkerJY b hind
  -- the integral coefficient family `A` of Navarro (3.16), collected over `IBr(Q)`
  obtain ⟨ωBT, hωBT⟩ : ∃ w : ℂ_[2], IsPrimitiveRoot w (Nat.card (↥C ⧸ Nz)) :=
    exists_isPrimitiveRoot_padicComplex 2 Nat.card_pos.ne'
  obtain ⟨A, ha0, hasum⟩ :=
    exists_intBlockCoeff (𝒪 := 𝓞_ℂ_[2]) (m := mQ) Nat.prime_two hϖ hϖ'
      (quotientPi_surjective πC hπC hlinC hNzP) (quotientPi_smul πC hπC hlinC hNzP) hkerJQ eQ
      hnilQ Nat.card_pos.ne' (fun g => pow_card_eq_one') hωBT
  -- Navarro (7.2)'s hypothesis for `Q`: every nontrivial `2`-element is conjugate to `ȳ`
  have hconjall : ∀ v : ↥C ⧸ Nz, IsPElement 2 v → v ≠ 1 → IsConj yb v := by
    intro v hv hv1
    have hvsq : v ^ 2 = 1 :=
      sq_eq_one_of_isPGroup_zpowers_quotient_centralizer T e hzT hz2 hz1 hzC
        (isPGroup_zpowers_of_isPElement hv)
    exact isConj_of_sq_eq_one_quotient_centralizer hO T e hTG hzT hz2 hz1 hzC hyb1
      (by rw [pow_two]; exact hyb2) hv1 hvsq
  -- Navarro (7.2): `|Irr(B_0(Q))| = 4` and `χ(ȳ) = ±1` there
  haveI := hMnorm
  have hquotM : IsPGroup 2 (↥(Subgroup.centralizer ({yb} : Set (↥C ⧸ Nz))) ⧸ M) :=
    IsPGroup.of_card (n := nM) (by rw [← Subgroup.index_eq_card, hMindex])
  have hweak := sum_character_mul_character_involution_eq_zero (𝒪 := 𝓞_ℂ_[2]) (nn := nnY)
    (hp := Nat.prime_two) (hx := hybP) (hω := hωY) (e := eY) (eG := eQ)
    (hπG := quotientPi_surjective πC hπC hlinC hNzP)
    (hlinG := quotientPi_smul πC hπC hlinC hNzP) (hπ := hπY) (hlin := hlinY) (hkerJ := hkerJY)
    (hnil := hnilY) (hnilG := hnilQ) (hω' := hω'Y) (hζ := hζ) (hζk := hζk) (hζK := hζK)
    (hconv := hconvC) (hNp := hMp) (hquot := hquotM) (S := SylC) (hφ₀ := hφ₀) (ht1 := hyb1)
    (hs := isPRegular_one Nat.prime_two)
  obtain ⟨hcard4, hpm⟩ := card_blockOfIrr_principal_eq_four_and_character_involution
    (𝒪 := 𝓞_ℂ_[2]) (nn := nnY)
    (hp := Nat.prime_two) (hx := hybP) (hω := hωY) (e := eY) (eG := eQ)
    (hπG := quotientPi_surjective πC hπC hlinC hNzP)
    (hlinG := quotientPi_smul πC hπC hlinC hNzP) (hπ := hπY) (hlin := hlinY) (hkerJ := hkerJY)
    (hnil := hnilY) (hnilG := hnilQ) (hω' := hω'Y) (hζ := hζ) (hζk := hζk) (hζK := hζK)
    (hconv := hconvC) (hNp := hMp) (hquot := hquotM) (S := SylC) (hφ₀ := hφ₀)
    (hy4 := by
      have h2 : yb ^ 2 = 1 := by rw [pow_two]; exact hyb2
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow])
    (hinv := ⟨1, by simpa using (inv_eq_of_mul_eq_one_right hyb2).symm⟩)
    (hconjall := hconjall) (ht1 := hyb1) (hweak := hweak) (hcart := hcart)
  -- the four members of `Irr(B_0(Q))`: the discarded `j₀` (sign `-1`), the trivial `l₀`, and two
  -- more `ψ₁`, `ψ₂` (Navarro (7.4))
  obtain ⟨j₀, hj₀B, hj₀neg⟩ := exists_character_involution_eq_neg_one (𝒪 := 𝓞_ℂ_[2]) (nn := nnY)
    (hp := Nat.prime_two) (hx := hybP) (hω := hωY) (e := eY) (eG := eQ)
    (hπG := quotientPi_surjective πC hπC hlinC hNzP)
    (hlinG := quotientPi_smul πC hπC hlinC hNzP) (hπ := hπY) (hlin := hlinY) (hkerJ := hkerJY)
    (hnil := hnilY) (hnilG := hnilQ) (hω' := hω'Y) (hζ := hζ) (hζk := hζk) (hζK := hζK)
    (hconv := hconvC) (hNp := hMp) (hquot := hquotM) (S := SylC) (hφ₀ := hφ₀)
    (ht := by rw [← pow_two] at hyb2 ⊢; exact hyb2) (hconjall := hconjall) (ht1 := hyb1)
    (hweak := hweak) (hcart := hcart)
  obtain ⟨l₀, hl₀B, hl₀⟩ :=
    exists_blockOfIrr_eq_principalBlock_character_eq_one (𝒪 := 𝓞_ℂ_[2]) (e := eQ)
      (hπG := quotientPi_surjective πC hπC hlinC hNzP)
      (hlinG := quotientPi_smul πC hπC hlinC hNzP) (hnilG := hnilQ)
  have hl₀ne : l₀ ≠ j₀ :=
    ne_of_character_involution_eq_neg_one eQ hl₀ hj₀neg
  obtain ⟨ψ₁, ψ₂, hψ₁B, hψ₂B, hψ₁ne, hψ₂ne, h01, h02, h12, henum⟩ :=
    exists_pair_of_card_filter_eq_four hcard4 hj₀B hl₀B hl₀ne
  -- the degree column and the column of values at `z`, as integer columns (段 341)
  obtain ⟨Tval, hTval⟩ := exists_intCast_character_of_involution (K := ℂ_[2]) eG
    (show z * z = 1 by rw [← pow_two]; exact hz2)
  have hgdeg : ∀ k, ((Fintype.card (mG k) : ℤ) : ℂ_[2])
      = (wedderburnRepresentation eG k).character 1 := fun k =>
    (character_one_eq_card eG k).symm
  -- the two odd basic-set degrees `ψ₁(1)`, `ψ₂(1)` (段 371)
  haveI : Fintype ↥((SQ : Subgroup (↥C ⧸ Nz))) := Fintype.ofFinite _
  have hSQsing : ∀ h : ↥((SQ : Subgroup (↥C ⧸ Nz))), (h : ↥C ⧸ Nz) ≠ 1 →
      ¬ IsPRegular 2 (h : ↥C ⧸ Nz) := by
    intro h h1 hreg
    obtain ⟨n, hn⟩ := SQ.isPGroup' h
    have hcoe : (h : ↥C ⧸ Nz) ^ 2 ^ n = 1 := by
      rw [← Subgroup.coe_pow, hn, Subgroup.coe_one]
    have hdvd := orderOf_dvd_of_pow_eq_one hcoe
    have hne1 : orderOf (h : ↥C ⧸ Nz) ≠ 1 := fun hc => h1 (orderOf_eq_one_iff.mp hc)
    obtain ⟨k, -, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact hne1 (by rw [hkeq, pow_zero])
    · exact hreg (hkeq ▸ dvd_pow_self 2 hpos.ne')
  obtain ⟨s₁, hs₁val, hs₁⟩ := exists_odd_intCast_principalBasicSet (𝒪 := 𝓞_ℂ_[2]) (nn := nnY)
    (hp := Nat.prime_two) (hx := hybP) (hω := hωY) (e := eY) (eG := eQ)
    (hπG := quotientPi_surjective πC hπC hlinC hNzP)
    (hlinG := quotientPi_smul πC hπC hlinC hNzP) (hπ := hπY) (hlin := hlinY) (hkerJ := hkerJY)
    (hnil := hnilY) (hnilG := hnilQ) (hω' := hω'Y) (hζ := hζ) (hζk := hζk) (hζK := hζK)
    (hconv := hconvC) (hNp := hMp) (hquot := hquotM) (S := SylC) (hφ₀ := hφ₀)
    (ht := by rw [← pow_two] at hyb2 ⊢; exact hyb2) (hconjall := hconjall) (ht1 := hyb1)
    (hcart := hcart) (P := (SQ : Subgroup (↥C ⧸ Nz)))
    (hPcard := by rw [← Nat.card_eq_fintype_card]; exact hSQ4)
    (hPsing := hSQsing) (hjB := hψ₁B) (hjne := hψ₁ne)
  obtain ⟨s₂, hs₂val, hs₂⟩ := exists_odd_intCast_principalBasicSet (𝒪 := 𝓞_ℂ_[2]) (nn := nnY)
    (hp := Nat.prime_two) (hx := hybP) (hω := hωY) (e := eY) (eG := eQ)
    (hπG := quotientPi_surjective πC hπC hlinC hNzP)
    (hlinG := quotientPi_smul πC hπC hlinC hNzP) (hπ := hπY) (hlin := hlinY) (hkerJ := hkerJY)
    (hnil := hnilY) (hnilG := hnilQ) (hω' := hω'Y) (hζ := hζ) (hζk := hζk) (hζK := hζK)
    (hconv := hconvC) (hNp := hMp) (hquot := hquotM) (S := SylC) (hφ₀ := hφ₀)
    (ht := by rw [← pow_two] at hyb2 ⊢; exact hyb2) (hconjall := hconjall) (ht1 := hyb1)
    (hcart := hcart) (P := (SQ : Subgroup (↥C ⧸ Nz)))
    (hPcard := by rw [← Nat.card_eq_fintype_card]; exact hSQ4)
    (hPsing := hSQsing) (hjB := hψ₂B) (hjne := hψ₂ne)
  -- the trivial character of `G`
  obtain ⟨i₀, hi₀B, hi₀⟩ :=
    exists_blockOfIrr_eq_principalBlock_character_eq_one (𝒪 := 𝓞_ℂ_[2]) (e := eG)
      (hπG := hπG) (hlinG := hlinG) (hnilG := hnilG)
  -- the three columns `D^t_0, D^t_1, D^t_2` of the analysis at `t`, over `ℤ` (段 370)
  obtain ⟨b, c, d, hbval, hcval, hdval, hbb, hcc, hdd, hbc, hbd, hcd, hgb, hgc, hgd,
      hb0, hc0, hd0, hT, hzero⟩ :=
    exists_intColumns_basicDecompositionNumber (𝒪 := 𝓞_ℂ_[2])
      (hp := Nat.prime_two) (hx := hzP) (hω := hωC) (hω' := hω'C) (hπ := hπC) (hlin := hlinC)
      (hkerJ := hkerJC) (hnilH := hnilC) (e := eC) (eG := eG) (hπG := hπG) (hlinG := hlinG)
      (hnilG := hnilG) (eQ := eQ) (hN := hNzP) (hcent := hcent) (hϖ := hϖ) (hϖ' := hϖ')
      (hyb := hybP) (hωC := hωY) (hω'C := hω'Y) (eC := eY) (hπC := hπY) (hlinC := hlinY)
      (hkerJC := hkerJY) (hnilC := hnilY) (hnilQ := hnilQ) (hζ := hζ) (hζk := hζk) (hζK := hζK)
      (hconvC := hconvC) (hconvG := hconvG) (hMp := hMp) (hquot := hquotM) (Syl := SylC)
      (hφ₀ := hφ₀) (hyb2 := hyb2) (A := A)
      (ht := by rw [← pow_two]; exact hz2) (hx1 := hz1) (hcardN := hNzcard) (ha0 := ha0)
      (hasum := hasum) (hconjall := hconjall) (hyb1 := hyb1) (hcart := hcart)
      (T := Tval) (gdeg := fun k => (Fintype.card (mG k) : ℤ)) (hTval := hTval) (hgdeg := hgdeg)
      (i₀ := i₀) (hi₀B := hi₀B) (hi₀ := hi₀) (j₀ := j₀) (l₀ := l₀) (ψ₁ := ψ₁) (ψ₂ := ψ₂)
      (s₁ := s₁) (s₂ := s₂) (hj₀ := hj₀B) (hl₀B := hl₀B) (hl₀ := hl₀) (hl₀ne := hl₀ne)
      (hψ₁B := hψ₁B) (hψ₁ne := hψ₁ne) (hψ₂B := hψ₂B) (hψ₂ne := hψ₂ne) (henum := henum)
      (h01 := h01) (h02 := h02) (h12 := h12) (hs₁val := hs₁val) (hs₂val := hs₂val)
  -- an element `y ∈ T` of order `4`, and the datum of `C_G(y)`
  have hq : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
  set w : ↥(T : Subgroup G) := e.symm (QuaternionGroup.a 1) with hwdef
  have hw2 : (w : G) ^ 2 ≠ 1 := by
    intro hcon
    refine hq ?_
    have hwsq : w ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hcon, Subgroup.coe_one])
    calc (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2
        = (e (e.symm (QuaternionGroup.a 1))) ^ 2 := by rw [e.apply_symm_apply]
      _ = e (w ^ 2) := by rw [map_pow, hwdef]
      _ = 1 := by rw [hwsq, map_one]
  have hyord : orderOf (w : G) = 4 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_four_of_quaternionTwo e (fun hcon => hw2 (by
      rw [← Subgroup.coe_pow, hcon, Subgroup.coe_one]))
  have hyC : (w : G) ∈ Subgroup.centralizer ({(w : G)} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun m hm => by
      rw [Set.mem_singleton_iff] at hm; subst hm; rfl
  haveI : Finite ↥(Subgroup.centralizer ({(w : G)} : Set G)) := Subtype.finite
  obtain ⟨ι'W, _, mW, _, _, _, eW, ιW, _, nnW, _, _, _, πW, hπW, hlinW, ωW, ω'W,
    hkerJW, hnilW, hωW, hω'W⟩ :=
    exists_datum_padicComplex 2 ↥(Subgroup.centralizer ({(w : G)} : Set G))
  have hcomplW := hasNormalPComplement_centralizer_orderFour T e w.2 hw2
  obtain ⟨MW, hMWnorm, hMWp, nMW, hMWindex⟩ := exists_normal_of_hasNormalPComplement hcomplW
  haveI := hMWnorm
  have hquotMW : IsPGroup 2 (↥(Subgroup.centralizer ({(w : G)} : Set G)) ⧸ MW) :=
    IsPGroup.of_card (n := nMW) (by rw [← Subgroup.index_eq_card, hMWindex])
  obtain ⟨SylW⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({(w : G)} : Set G))) := Sylow.nonempty
  have hSylW4 : Nat.card ↥(SylW : Subgroup ↥(Subgroup.centralizer ({(w : G)} : Set G))) = 4 := by
    rw [sylow_centralizer_eq_zpowers T e w.2 hw2 hyC SylW, Nat.card_zpowers,
      ← Subgroup.orderOf_coe]
    exact hyord
  obtain ⟨φ₀W, hφ₀W⟩ := Quotient.exists_rep (principalBlock πW hπW hlinW hnilW)
  have hcartW : cartanMatrix (𝒪 := 𝓞_ℂ_[2]) (nn := nnW) Nat.prime_two hωW hω'W hπW hlinW hkerJW
      eW φ₀W φ₀W = 4 := by
    rw [cartanMatrix_principalBlock_eq_card_sylow_of_hasNormalPComplement Nat.prime_two hωW hω'W
      hπW hlinW hkerJW hnilW eW hcomplW SylW hφ₀W, hSylW4]
  -- the converse third main theorem for `(G, C_G(y))`, and the column `D^y_0` (段 348)
  have hwP : IsPElement 2 (w : G) := ⟨2, by rw [hyord]; norm_num⟩
  have hconvW := fun bl hind =>
    eq_principalBlock_of_inducedBlockOfCentralizer_eq_of_roots (K := ℂ_[2]) Nat.prime_two hwP
      hroot hroot' hζ hζk hζK eG eW hπG hlinG hnilG hkerJG hπW hlinW hnilW hkerJW bl hind
  have hw1 : (w : G) ≠ 1 := fun hcon => hw2 (by rw [hcon, one_pow])
  obtain ⟨a, hava, haa, hga, ha0⟩ :=
    exists_intColumn_generalizedDecompositionNumber_principalBlock (𝒪 := 𝓞_ℂ_[2]) (nn := nnW)
      (hp := Nat.prime_two) (hx := hwP) (hω := hωW) (e := eW) (eG := eG) (hπG := hπG)
      (hlinG := hlinG) (hπ := hπW) (hlin := hlinW) (hkerJ := hkerJW) (hnil := hnilW)
      (hnilG := hnilG) (hω' := hω'W) (hζ := hζ) (hζk := hζk) (hζK := hζK) (hconv := hconvW)
      (hNp := hMWp) (hquot := hquotMW) (S := SylW) (hφ₀ := hφ₀W)
      (hy4 := by
        have h := pow_orderOf_eq_one (w : G)
        rwa [hyord] at h)
      (hinv := by
        obtain ⟨g, hg⟩ := exists_conj_eq_inv_of_quaternionTwo e
          (fun hcon => hw2 (by rw [← Subgroup.coe_pow, hcon, Subgroup.coe_one]))
        exact ⟨(g : G), by
          have := congrArg (Subtype.val (p := fun x => x ∈ (T : Subgroup G))) hg
          push_cast at this
          exact this⟩)
      (ht1 := hw1) (hcart := hcartW)
  -- Navarro p. 141, equation (4): the column at `y` is orthogonal to the columns at `t`
  have hxy : ¬ IsConj z (w : G) := fun hcon => by
    obtain ⟨u, hu⟩ := hcon
    have hord := SemiconjBy.orderOf_eq (u : G) hu
    rw [hyord, hz] at hord
    omega
  have hcross : ∀ (η : ι'Q) (col : ι'G → ℤ),
      (∀ k, basicDecompositionNumber
        (generalizedDecompositionNumber z Nat.prime_two hω'C hπC hlinC hkerJC
          ((wedderburnRepresentation eG k).character)
          (fun _ _ h => character_eq_of_isConj _ h))
        (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : ℂ_[2])) η = ((col k : ℤ) : ℂ_[2])) →
      (∑ k, a k * col k) = 0 := by
    intro η col hcolval
    refine sum_mul_eq_of_intCast (fun k => (hava k).symm) (fun k => hcolval k) ?_
    rw [Int.cast_zero]
    exact sum_generalizedDecompositionNumber_mul_basicDecompositionNumber_eq_zero
      (hp := Nat.prime_two) (hω' := hω'C) (hπ := hπC) (hlin := hlinC) (hkerJ := hkerJC)
      (eG := eG) (hωY' := hω'W) (hπY := hπW) (hlinY := hlinW) (hkerJY := hkerJW)
      (u := fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : ℂ_[2]))
      (ht := by rw [← pow_two]; exact hz2) (hx := hzP) (hy := hwP) (hxy := hxy)
      (φ := φ₀W) (η := η)
  have hab : (∑ k, a k * b k) = 0 := hcross l₀ b hbval
  have hac : (∑ k, a k * c k) = 0 := hcross ψ₁ c hcval
  have had : (∑ k, a k * d k) = 0 := hcross ψ₂ d hdval
  -- off `Irr(B_0(G))` the column at `y` vanishes too, so `hzero` covers all four columns
  have hzeroA : ∀ k, ¬ (blockOfIrr eG hπG hlinG hnilG k = principalBlock πG hπG hlinG hnilG) →
      a k = 0 := by
    intro k hk
    refine Int.cast_injective (α := ℂ_[2]) ?_
    rw [hava k, Int.cast_zero]
    exact generalizedDecompositionNumber_principalBlock_eq_zero_of_blockOfIrr_ne
      (hp := Nat.prime_two) (hx := hwP) (hω := hωW) (e := eW) (eG := eG) (hπG := hπG)
      (hlinG := hlinG) (hπ := hπW) (hlin := hlinW) (hkerJ := hkerJW) (hnil := hnilW)
      (hnilG := hnilG) (hω' := hω'W) (hζ := hζ) (hζk := hζk) (hζK := hζK) (hφ₀ := hφ₀W)
      (hi := hk)
  -- on `Irr(B_0(G))` the column at `y` *is* the character value `χ(y)`
  have havaB : ∀ k, blockOfIrr eG hπG hlinG hnilG k = principalBlock πG hπG hlinG hnilG →
      ((a k : ℤ) : ℂ_[2]) = (wedderburnRepresentation eG k).character (w : G) := by
    intro k hk
    rw [hava k]
    exact (character_involution_eq_generalizedDecompositionNumber (𝒪 := 𝓞_ℂ_[2]) (nn := nnW)
      (hp := Nat.prime_two) (hx := hwP) (hω := hωW) (hω' := hω'W) (e := eW) (eG := eG)
      (hπG := hπG) (hlinG := hlinG) (hπ := hπW) (hlin := hlinW) (hkerJ := hkerJW)
      (hnil := hnilW) (hnilG := hnilG) (hζ := hζ) (hζk := hζk) (hζK := hζK) (hconv := hconvW)
      (hNp := hMWp) (hquot := hquotMW) (S := SylW) (hφ₀ := hφ₀W) (hj := hk)).symm
  -- `χ(y) ≡ χ(t) mod 2` (段 289), hence `hcong`
  obtain ⟨ωG', hωG'⟩ : ∃ v : ℂ_[2], IsPrimitiveRoot v (Nat.card G) :=
    exists_isPrimitiveRoot_padicComplex 2 Nat.card_pos.ne'
  have hcong : ∀ k, blockOfIrr eG hπG hlinG hnilG k = principalBlock πG hπG hlinG hnilG →
      (2 : ℤ) ∣ (a k + Tval k) := by
    intro k hk
    refine OddOrder.Algebra.two_dvd_add_of_modEq ?_
    exact OddOrder.RepresentationTheory.intModEq_of_isPElement_of_isPElement
      (hm := Nat.card_pos) (hωm := hωG') (hgm := fun g => pow_card_eq_one')
      (hω := hωG'.isIntegral Nat.card_pos) (hp := Nat.prime_two)
      (hχ := OddOrder.RepresentationTheory.le_adjoinSpan
        (mem_virtualCharacters_wedderburnRepresentation eG k))
      (hu := hwP) (hv := hzP) (ha := (havaB k hk).symm) (hb := (hTval k).symm)
      (hc := (character_one_eq_card eG k))
  -- Burnside's relation (10) (段 330/332/335/336)
  have hzuniq := unique_involution_of_quaternionSylow T e hzT hz2 hz1
  have hwa : (∑ k, classSquareCoeff eG (ConjClasses.mk z) k * ((a k : ℤ) : ℂ_[2])) = 0 := by
    rw [Finset.sum_congr rfl fun k _ => by rw [hava k]]
    exact sum_classSquareCoeff_mul_generalizedDecompositionNumber_eq_zero (𝒪 := 𝓞_ℂ_[2])
      (nn := nnW) eG hπW hlinW hkerJW hω'W T hzuniq hz hwP hw1 φ₀W
  have hwcol : ∀ (η : ι'Q) (col : ι'G → ℤ),
      (∀ k, basicDecompositionNumber
        (generalizedDecompositionNumber z Nat.prime_two hω'C hπC hlinC hkerJC
          ((wedderburnRepresentation eG k).character)
          (fun _ _ h => character_eq_of_isConj _ h))
        (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : ℂ_[2])) η = ((col k : ℤ) : ℂ_[2])) →
      (∑ k, classSquareCoeff eG (ConjClasses.mk z) k * ((col k : ℤ) : ℂ_[2])) = 0 := by
    intro η col hcolval
    rw [Finset.sum_congr rfl fun k _ => by rw [← hcolval k]]
    exact sum_classSquareCoeff_mul_basicDecompositionNumber_eq_zero (𝒪 := 𝓞_ℂ_[2]) (nn := nnC)
      eG hπC hlinC hkerJC hω'C T hzuniq hz hzP hz1
      (fun μ l => ((intBasicSetMatrix eQ A yb j₀ μ l : ℤ) : ℂ_[2])) η
  have hm0 : ((OddOrder.RepresentationTheory.conjugacyClassSize (ConjClasses.mk z) : ℕ)
      : ℂ_[2]) ^ 2 ≠ 0 := by
    refine pow_ne_zero _ (Nat.cast_ne_zero.mpr ?_)
    exact (OddOrder.RepresentationTheory.conjugacyClassSize_pos (ConjClasses.mk z)).ne'
  have hwg : ∀ k, classSquareCoeff eG (ConjClasses.mk z) k
      * ((Fintype.card (mG k) : ℤ) : ℂ_[2])
      = ((OddOrder.RepresentationTheory.conjugacyClassSize (ConjClasses.mk z) : ℕ) : ℂ_[2]) ^ 2
        * ((Tval k : ℤ) : ℂ_[2]) ^ 2 := by
    intro k
    rw [hgdeg k, hTval k, classSquareCoeff_mul_character_one eG (ConjClasses.mk z) k,
      character_eq_of_isConj (wedderburnRepresentation eG k)
        (ConjClasses.mk_eq_mk_iff_isConj.mp
          (OddOrder.RepresentationTheory.conjClass_mk_out (ConjClasses.mk z)))]
  have hwi₀ : classSquareCoeff eG (ConjClasses.mk z) i₀
      = ((OddOrder.RepresentationTheory.conjugacyClassSize (ConjClasses.mk z) : ℕ) : ℂ_[2]) ^ 2 :=
    classSquareCoeff_of_character_eq_one eG (ConjClasses.mk z) hi₀
  have h10 : ∀ v : ι'G → ℤ, (∀ k, 2 * v k = a k + b k - c k - d k) →
      ∀ i j : ι'G, i ≠ i₀ → j ≠ i₀ → i ≠ j → v i = 1 → v j = -1 →
        (∀ k, k ≠ i₀ → k ≠ i → k ≠ j → v k = 0) →
        (Fintype.card (mG i) : ℤ) * (Fintype.card (mG j) : ℤ)
          + Tval i ^ 2 * (Fintype.card (mG j) : ℤ)
          - Tval j ^ 2 * (Fintype.card (mG i) : ℤ) = 0 := by
    intro v hv i j hii₀ hji₀ hij hvi hvj hvoff
    have hv0 : v i₀ = 1 := by
      have h := hv i₀
      rw [ha0 i₀ hi₀B hi₀, hb0, hc0, hd0] at h
      omega
    have hzero : (∑ k, classSquareCoeff eG (ConjClasses.mk z) k * ((v k : ℤ) : ℂ_[2])) = 0 :=
      OddOrder.Algebra.sum_mul_halfSum_eq_zero two_ne_zero
        (fun k => by
          have h := hv k
          have : ((2 * v k : ℤ) : ℂ_[2]) = ((a k + b k - c k - d k : ℤ) : ℂ_[2]) := by rw [h]
          push_cast at this
          linear_combination this)
        hwa (hwcol l₀ b hbval) (hwcol ψ₁ c hcval) (hwcol ψ₂ d hdval)
    have hten := OddOrder.Algebra.sign_relation_ten (δ₁ := 1) (δ₂ := -1) hm0 hii₀ hji₀ hij hwg
      hwi₀ (by rw [hv0]; norm_num) (by rw [hvi]; norm_num) (by rw [hvj]; norm_num)
      (fun k h1 h2 h3 => by rw [hvoff k h1 h2 h3]; norm_num) hzero
    refine Int.cast_injective (α := ℂ_[2]) ?_
    push_cast at hten ⊢
    linear_combination hten
  sorry

end OddOrder.GroupTheory
