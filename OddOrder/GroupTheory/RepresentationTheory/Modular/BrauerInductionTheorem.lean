/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.DivisibleClassFunction
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerInductionDescent
import OddOrder.GroupTheory.RepresentationTheory.Modular.CharacterPClassCongruence

/-!
# Gorenstein Lemmas 7.8–7.10: `v(G) = ch(G)`

The last three steps of the Brauer–Tate argument.

* **Lemma 7.8**: for each prime `p` there is an integer-valued `χ ∈ v_R(G)` with `χ ≡ 1 (mod p)`
  everywhere.  One indicator `ζ_C` (Lemma 7.6) per `p`-regular class `C`, taken with `P` a Sylow
  `p`-subgroup of `C_G(u_C)` so that `ζ_C(u_C) = [C_G(u_C) : P]` is prime to `p`; scale by the
  inverse of that value modulo `p` and add up.  **Lemma 7.5** is what makes this work off the
  chosen representatives: `ζ_C` is integer-valued and lies in `ch_R(G)`, hence is constant modulo
  `p` on the whole `p`-class.
* **Lemma 7.9**: `|G| = m p^a` with `p ∤ m` gives `m · 1_G ∈ v(G)`.  Raise the `χ` of Lemma 7.8 to
  the power `p^a` (`v_R(G)` is an ideal of `ch_R(G)`) to get `ζ ≡ 1 (mod p^a)`; then
  `m(1_G − ζ)` has all values divisible by `m p^a = |G|`, so lies in `v_R(G)` by **Lemma 7.7**,
  and `m · 1_G = m(1_G − ζ) + m ζ ∈ v_R(G)`.  Finally **Lemma 7.4** descends to `v(G)`.
* **Lemma 7.10**: the `m_i = |G| / p_i^{a_i}` are collectively coprime, so `1_G ∈ v(G)`, and since
  `v(G)` is an ideal of `ch(G)` (**Lemma 7.3**) this gives `v(G) = ch(G)`.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_congr_one_mod_prime` — **Lemma 7.8**

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemmas 7.8–7.10 (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory.Modular

open OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {K G : Type*} [Field K] [CharZero K] [Group G] [Fintype G] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  [Finite ι'] [Invertible (Nat.card G : K)]
  {N : ℕ} {ω : K} {𝒳 : Set (Subgroup G)}

include e in
/-- **Gorenstein Lemma 7.8.**  For every prime `p` there is an integer-valued element of `v_R(G)`
congruent to `1` modulo `p` at every element of `G`. -/
theorem exists_congr_one_mod_prime (h𝒳 : IsElementaryFamily 𝒳) (hN : N ≠ 0)
    (hgN : ∀ g : G, g ^ N = 1) (hωN : IsPrimitiveRoot ω N) {p : ℕ} (hp : p.Prime) :
    ∃ (χ : G → K) (b : G → ℤ), χ ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳) ∧
      (∀ y : G, χ y = (b y : K)) ∧ ∀ y : G, b y ≡ 1 [ZMOD (p : ℤ)] := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hωint : IsIntegral ℤ ω := isIntegral_of_pow_eq_one hN hωN.pow_eq_one
  -- one `p`-regular representative per class: the `p'`-part of the chosen representative
  obtain ⟨u, hu⟩ : ∃ f : ConjClasses G → G, ∀ C, f C = pRegularPart p C.out := ⟨_, fun _ => rfl⟩
  have hureg : ∀ C : ConjClasses G, IsPRegular p (u C) := fun C => by
    rw [hu]; exact isPRegular_pRegularPart hp (isOfFinOrder_of_finite _)
  -- a Sylow `p`-subgroup of each centraliser, transported into `G`
  have hPex : ∀ C : ConjClasses G, ∃ P : Subgroup G, IsPGroup p ↥P ∧
      P ≤ Subgroup.centralizer ({u C} : Set G) ∧
      Nat.card ↥P = ordProj[p] (Nat.card ↥(Subgroup.centralizer ({u C} : Set G))) := by
    intro C
    obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime
      (G := ↥(Subgroup.centralizer ({u C} : Set G))) p (Nat.ordProj_dvd _ _)
    exact ⟨Q.map (Subgroup.centralizer ({u C} : Set G)).subtype, (IsPGroup.of_card hQ).map _,
      Subgroup.map_subtype_le Q, (Subgroup.card_subtype _ Q).trans hQ⟩
  choose P hPp hPle hPcard using hPex
  have hcomm : ∀ C : ConjClasses G, ∀ v ∈ P C, Commute (u C) v := fun C v hv =>
    (Subgroup.mem_centralizer_iff.mp (hPle C hv)) (u C) rfl
  -- Lemma 7.6 for each class
  have hex : ∀ C : ConjClasses G, ∃ χ : G → K,
      χ ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳) ∧
      (∀ y : G, χ y = ((conjugateCount (leftCosetOf (u C) (P C)) y /
        Nat.card ↥(P C) : ℕ) : K)) ∧
      (∀ y z : G, IsConj y z → χ y = χ z) ∧
      (∀ y : G, ¬ IsConj (pRegularPart p y) (u C) → χ y = 0) ∧
      χ (u C) = ((Nat.card ↥(Subgroup.centralizer ({u C} : Set G)) /
        Nat.card ↥(P C) : ℕ) : K) :=
    fun C => exists_pClassIndicator h𝒳 hN hgN hωN hp (hureg C) (hPp C) (hcomm C)
  choose ζ hζmem hζval hζcf hζsupp hζself using hex
  obtain ⟨nval, hnval⟩ : ∃ f : ConjClasses G → G → ℕ, ∀ C y,
      f C y = conjugateCount (leftCosetOf (u C) (P C)) y / Nat.card ↥(P C) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨mval, hmval⟩ : ∃ f : ConjClasses G → ℕ, ∀ C,
      f C = Nat.card ↥(Subgroup.centralizer ({u C} : Set G)) / Nat.card ↥(P C) :=
    ⟨_, fun _ => rfl⟩
  have hζvalK : ∀ C y, ζ C y = (nval C y : K) := fun C y => by rw [hnval]; exact hζval C y
  have hζvalZ : ∀ C y, ζ C y = (((nval C y : ℕ) : ℤ) : K) := fun C y => by
    rw [hζvalK C y]; push_cast; ring
  have hζselfK : ∀ C, ζ C (u C) = (mval C : K) := fun C => by rw [hmval]; exact hζself C
  -- `[C_G(u C) : P C]` is prime to `p`, so it is invertible modulo `p`
  have hmcop : ∀ C : ConjClasses G, ¬ p ∣ mval C := fun C => by
    rw [hmval, hPcard C]
    exact Nat.not_dvd_ordCompl hp Nat.card_pos.ne'
  obtain ⟨a, hacoef⟩ : ∃ f : ConjClasses G → ℤ, ∀ C, f C = Nat.gcdA (mval C) p :=
    ⟨_, fun _ => rfl⟩
  have hinv : ∀ C : ConjClasses G, a C * (mval C : ℤ) ≡ 1 [ZMOD (p : ℤ)] := by
    intro C
    have hcop : Nat.gcd (mval C) p = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr (hmcop C))
    have hbez := Nat.gcd_eq_gcd_ab (mval C) p
    rw [hcop] at hbez
    refine Int.modEq_iff_dvd.mpr ⟨Nat.gcdB (mval C) p, ?_⟩
    rw [hacoef]
    push_cast at hbez ⊢
    linarith
  obtain ⟨S, hS⟩ : ∃ S : Finset (ConjClasses G), ∀ C, C ∈ S ↔ IsPRegularClass p C :=
    ⟨Finset.univ.filter fun C => IsPRegularClass p C, fun C => by simp⟩
  -- on a `p`-regular class the chosen `p'`-part still represents the class
  have hmkout : ∀ C : ConjClasses G, ConjClasses.mk C.out = C := fun C => by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  have hmku : ∀ C : ConjClasses G, IsPRegularClass p C → ConjClasses.mk (u C) = C := by
    intro C hC
    rw [hu, ← pRegularPartClass_mk C.out, hmkout C]
    exact pRegularPartClass_of_isPRegularClass hp hC
  refine ⟨∑ C ∈ S, a C • ζ C, fun y => ∑ C ∈ S, a C * (nval C y : ℤ),
    AddSubgroup.sum_mem _ fun C _ => AddSubgroup.zsmul_mem _ (hζmem C) (a C), fun y => ?_,
    fun y => ?_⟩
  · change (∑ C ∈ S, a C • ζ C) y = ((∑ C ∈ S, a C * (nval C y : ℤ) : ℤ) : K)
    rw [Finset.sum_apply, Int.cast_sum]
    exact Finset.sum_congr rfl fun C _ => by
      rw [Pi.smul_apply, zsmul_eq_mul, hζvalK C y, Int.cast_mul, Int.cast_natCast]
  -- the congruence: only the `p`-class of `y` contributes
  · change (∑ C ∈ S, a C * (nval C y : ℤ)) ≡ 1 [ZMOD (p : ℤ)]
    have hDreg : IsPRegularClass p (ConjClasses.mk (pRegularPart p y)) :=
      isPRegularClass_mk.mpr (isPRegular_pRegularPart hp (isOfFinOrder_of_finite y))
    obtain ⟨D, hD⟩ : ∃ D : ConjClasses G, ConjClasses.mk (pRegularPart p y) = D := ⟨_, rfl⟩
    have hDS : D ∈ S := (hS D).mpr (hD ▸ hDreg)
    have hzero : ∀ C ∈ S, C ≠ D → a C * (nval C y : ℤ) = 0 := by
      intro C hC hCD
      have hne : ¬ IsConj (pRegularPart p y) (u C) := fun h =>
        hCD ((hmku C ((hS C).mp hC)).symm.trans
          ((ConjClasses.mk_eq_mk_iff_isConj.mpr h).symm.trans hD))
      have hz : (nval C y : K) = 0 := by rw [← hζvalK C y]; exact hζsupp C y hne
      rw [Nat.cast_eq_zero] at hz
      rw [hz, Nat.cast_zero, mul_zero]
    rw [Finset.sum_eq_single_of_mem D hDS hzero]
    -- Lemma 7.5: the indicator is constant modulo `p` on the `p`-class
    have hconj : IsConj (pRegularPart p y) (u D) :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hD.trans (hmku D ((hS D).mp hDS)).symm)
    have hval : (nval D (pRegularPart p y) : ℤ) = (mval D : ℤ) := by
      have hK : ((nval D (pRegularPart p y) : ℕ) : K) = ((mval D : ℕ) : K) := by
        rw [← hζvalK D _, ← hζselfK D]
        exact hζcf D _ (u D) hconj
      exact_mod_cast hK
    have hmem : ζ D ∈ adjoinSpan ω (virtualCharacters K G) :=
      adjoinSpan_mono (inducedVirtualCharacters_le_virtualCharacters e 𝒳) (hζmem D)
    have hcong : (nval D y : ℤ) ≡ (nval D (pRegularPart p y) : ℤ) [ZMOD (p : ℤ)] :=
      intModEq_of_mem_adjoinSpan (Nat.pos_of_ne_zero hN) hωN hgN hωint hp hmem y
        (hζvalZ D y) (hζvalZ D _)
    rw [hval] at hcong
    exact (hcong.mul_left (a D)).trans (hinv D)

end OddOrder.RepresentationTheory.Modular
