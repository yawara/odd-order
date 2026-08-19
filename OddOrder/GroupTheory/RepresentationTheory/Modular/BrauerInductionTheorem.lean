/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.DivisibleClassFunction
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerInductionDescent
import OddOrder.GroupTheory.RepresentationTheory.Modular.CharacterPClassCongruence

/-!
# Gorenstein Lemmas 7.8–7.10 and Brauer's characterization of characters

The last three steps of the Brauer–Tate argument, and the theorem they were for.

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
* **Theorem 7.1 (Brauer–Tate)**: a class function whose restriction to every `E ∈ 𝒳` is a virtual
  character is `1_G · θ`, and the projection formula (**Lemma 7.2**) pushes `θ` inside each
  induction, so `θ ∈ v(G)`.

⚠ The classical statement asks the restrictions to be virtual on the *elementary* subgroups; here
`𝒳` is a parameter and the only thing used about it is `IsElementaryFamily` (it contains every
`⟨u⟩ P`), which is what Lemma 7.6 needs.  A larger `𝒳` makes the hypothesis stronger and the
conclusion stronger in the same measure.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_congr_one_mod_prime` — **Lemma 7.8**
* `OddOrder.RepresentationTheory.Modular.zsmul_one_mem_inducedVirtualCharacters` — **Lemma 7.9**
* `OddOrder.RepresentationTheory.Modular.inducedVirtualCharacters_eq_virtualCharacters` —
  **Lemma 7.10**, `v(G) = ch(G)`
* `OddOrder.RepresentationTheory.Modular.mem_inducedVirtualCharacters_of_restrict` —
  **Brauer's characterization of characters**

## References

* D. Gorenstein, *Finite Groups*, §4.7, Theorem 7.1 and Lemmas 7.8–7.10
  (`references/gorenstein/pages/`).
-/

namespace OddOrder.RepresentationTheory.Modular

open OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {K G : Type*} [Field K] [CharZero K] [Group G] [Fintype G] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  [Finite ι'] [Invertible (Nat.card G : K)]
  {N : ℕ} {ω : K} {𝒳 : Set (Subgroup G)}

include e in
set_option backward.isDefEq.respectTransparency false in
/-- **Gorenstein Lemma 7.8.**  For every prime `p` there is an integer-valued element of `v_R(G)`
congruent to `1` modulo `p` at every element of `G`. -/
theorem exists_congr_one_mod_prime (h𝒳 : IsElementaryFamily 𝒳) (hN : N ≠ 0)
    (hgN : ∀ g : G, g ^ N = 1) (hωN : IsPrimitiveRoot ω N) {p : ℕ} (hp : p.Prime) :
    ∃ (χ : G → K) (b : G → ℤ), χ ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳) ∧
      (∀ y : G, χ y = (b y : K)) ∧ (∀ y z : G, IsConj y z → χ y = χ z) ∧
      ∀ y : G, b y ≡ 1 [ZMOD (p : ℤ)] := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
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
    fun y z hyz => ?_, fun y => ?_⟩
  · change (∑ C ∈ S, a C • ζ C) y = ((∑ C ∈ S, a C * (nval C y : ℤ) : ℤ) : K)
    rw [Finset.sum_apply, Int.cast_sum]
    exact Finset.sum_congr rfl fun C _ => by
      rw [Pi.smul_apply, zsmul_eq_mul, hζvalK C y, Int.cast_mul, Int.cast_natCast]
  · rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun C _ => by
      rw [Pi.smul_apply, Pi.smul_apply, hζcf C y z hyz]
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

/-! ### Lemma 7.9 -/

omit [CharZero K] [Finite ι'] [Invertible (Nat.card G : K)] in
/-- **The `ℤ[ω]`-coefficient form of Lemma 7.3**: `v_R(G)` is an ideal of `ch_R(G)`.  On generators
`(ω^i · w) · (ω^j · θ) = ω^{i+j} · (w θ)`, and `w θ ∈ v(G)` by Lemma 7.3. -/
theorem mul_mem_adjoinSpan_inducedVirtualCharacters {w θ : G → K}
    (hw : w ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳))
    (hθ : θ ∈ adjoinSpan ω (virtualCharacters K G)) :
    w * θ ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳) := by
  induction hθ using AddSubgroup.closure_induction with
  | mem x hx =>
      obtain ⟨j, θ₀, hθ₀, rfl⟩ := hx
      induction hw using AddSubgroup.closure_induction with
      | mem y hy =>
          obtain ⟨i, w₀, hw₀, rfl⟩ := hy
          have hprod : (ω ^ i • w₀) * (ω ^ j • θ₀) = ω ^ (i + j) • (w₀ * θ₀) := by
            funext g
            simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, pow_add]
            ring
          rw [hprod]
          exact pow_smul_mem_adjoinSpan _ (mul_mem_inducedVirtualCharacters hw₀ hθ₀)
      | zero => simpa only [zero_mul] using AddSubgroup.zero_mem _
      | add a b _ _ ha hb => simpa only [add_mul] using AddSubgroup.add_mem _ ha hb
      | neg a _ ha => simpa only [neg_mul] using AddSubgroup.neg_mem _ ha
  | zero => simpa only [mul_zero] using AddSubgroup.zero_mem _
  | add a b _ _ ha hb => simpa only [mul_add] using AddSubgroup.add_mem _ ha hb
  | neg a _ ha => simpa only [mul_neg] using AddSubgroup.neg_mem _ ha

include e in
/-- **Gorenstein Lemma 7.9.**  Writing `|G| = m p^a` with `p ∤ m`, the class function `m · 1_G`
lies in `v(G)`.  Raise the `χ` of Lemma 7.8 to the power `p^a`: the result `ζ` is still in
`v_R(G)` (Lemma 7.3) and now satisfies `ζ ≡ 1 (mod p^a)`, so all values of `m(1_G − ζ)` are
divisible by `m p^a = |G|` and Lemma 7.7 applies. -/
theorem zsmul_one_mem_inducedVirtualCharacters (h𝒳 : IsElementaryFamily 𝒳) (hN : N ≠ 0)
    (hgN : ∀ g : G, g ^ N = 1) (hωN : IsPrimitiveRoot ω N) {p : ℕ} (hp : p.Prime) :
    ((ordCompl[p] (Nat.card G) : ℕ) : ℤ) • (1 : G → K) ∈ inducedVirtualCharacters K 𝒳 := by
  classical
  have hωint : IsIntegral ℤ ω := isIntegral_of_pow_eq_one hN hωN.pow_eq_one
  obtain ⟨χ, b, hχmem, hχval, hχcf, hχcong⟩ := exists_congr_one_mod_prime e h𝒳 hN hgN hωN hp
  have hχch : χ ∈ adjoinSpan ω (virtualCharacters K G) :=
    adjoinSpan_mono (inducedVirtualCharacters_le_virtualCharacters e 𝒳) hχmem
  -- `v_R(G)` is an ideal of `ch_R(G)`, so it is closed under positive powers
  have hpow : ∀ k : ℕ, χ ^ (k + 1) ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳) := by
    intro k
    induction k with
    | zero => simpa using hχmem
    | succ k ih => rw [pow_succ]; exact mul_mem_adjoinSpan_inducedVirtualCharacters ih hχch
  obtain ⟨t, ht⟩ : ∃ t : ℕ, p ^ (Nat.card G).factorization p = t + 1 :=
    ⟨p ^ (Nat.card G).factorization p - 1, by
      have := Nat.one_le_pow ((Nat.card G).factorization p) p hp.pos; omega⟩
  have hζmem : χ ^ (p ^ (Nat.card G).factorization p) ∈
      adjoinSpan ω (inducedVirtualCharacters K 𝒳) := ht ▸ hpow t
  -- `ζ(y) = b(y)^{p^a} ≡ 1 (mod p^a)`
  have hζval : ∀ y : G, (χ ^ (p ^ (Nat.card G).factorization p)) y
      = ((b y ^ p ^ (Nat.card G).factorization p : ℤ) : K) := fun y => by
    rw [Pi.pow_apply, hχval y]; push_cast; ring
  have hζdvd : ∀ y : G, ((p : ℤ) ^ (Nat.card G).factorization p)
      ∣ b y ^ p ^ (Nat.card G).factorization p - 1 := by
    intro y
    have hstep := dvd_sub_pow_of_dvd_sub (R := ℤ) (p := p) (a := b y) (b := 1)
      (hχcong y).symm.dvd ((Nat.card G).factorization p)
    rw [one_pow] at hstep
    exact dvd_trans (pow_dvd_pow _ (Nat.le_succ _)) hstep
  choose k hk using hζdvd
  -- `m p^a = |G|`
  have hmp : ((p : ℤ) ^ (Nat.card G).factorization p) * ((ordCompl[p] (Nat.card G) : ℕ) : ℤ)
      = (Nat.card G : ℤ) := by
    have := Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) this
  -- `m (1_G − ζ)` is a class function with all values divisible by `|G|`
  have hdiff : ((ordCompl[p] (Nat.card G) : ℕ) : ℤ) •
      ((1 : G → K) - χ ^ (p ^ (Nat.card G).factorization p))
      ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳) := by
    refine mem_adjoinSpan_inducedVirtualCharacters_of_card_dvd h𝒳 hN hgN hωN ?_ ?_
    · intro y z hyz
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, Pi.pow_apply, hχcf y z hyz]
    · intro y
      refine ⟨-(k y), ?_⟩
      have hval : (((1 : G → K) - χ ^ (p ^ (Nat.card G).factorization p)) y)
          = ((1 - b y ^ p ^ (Nat.card G).factorization p : ℤ) : K) := by
        rw [Pi.sub_apply, Pi.one_apply, hζval y]; push_cast; ring
      rw [Pi.smul_apply, hval, zsmul_eq_mul]
      have hkey : ((ordCompl[p] (Nat.card G) : ℕ) : ℤ)
            * (1 - b y ^ p ^ (Nat.card G).factorization p)
          = -(k y) * (Nat.card G : ℤ) := by
        rw [← hmp]
        linear_combination (-(((ordCompl[p] (Nat.card G) : ℕ) : ℤ))) * (hk y)
      exact_mod_cast congrArg (fun n : ℤ => (n : K)) hkey
  -- `m · 1_G = m(1_G − ζ) + m ζ`
  have hmem : ((ordCompl[p] (Nat.card G) : ℕ) : ℤ) • (1 : G → K)
      ∈ adjoinSpan ω (inducedVirtualCharacters K 𝒳) := by
    have hsum := AddSubgroup.add_mem _ hdiff (AddSubgroup.zsmul_mem _ hζmem
      ((ordCompl[p] (Nat.card G) : ℕ) : ℤ))
    rwa [← smul_add, sub_add_cancel] at hsum
  exact mem_inducedVirtualCharacters_of_mem_adjoinSpan e hωint
    (AddSubgroup.zsmul_mem _ one_mem_virtualCharacters _) hmem

/-! ### Lemma 7.10 -/

include e in
/-- **`1_G ∈ v(G)`.**  The `ordCompl[q] |G|` (`q` prime) all lie in the ideal
`{k : ℤ | k · 1_G ∈ v(G)}` by Lemma 7.9, and their gcd is `1`: a common prime divisor `q` would
divide `ordCompl[q] |G|`. -/
theorem one_mem_inducedVirtualCharacters (h𝒳 : IsElementaryFamily 𝒳) (hN : N ≠ 0)
    (hgN : ∀ g : G, g ^ N = 1) (hωN : IsPrimitiveRoot ω N) :
    (1 : G → K) ∈ inducedVirtualCharacters K 𝒳 := by
  classical
  have hn0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  -- the multiples of `1_G` lying in `v(G)` form an ideal of `ℤ`
  have hmul : ∀ j k : ℤ, k • (1 : G → K) ∈ inducedVirtualCharacters K 𝒳 →
      (j * k) • (1 : G → K) ∈ inducedVirtualCharacters K 𝒳 := fun j k hk => by
    rw [mul_smul]; exact AddSubgroup.zsmul_mem _ hk j
  have hgcd : ∀ x y : ℕ, ((x : ℤ) • (1 : G → K) ∈ inducedVirtualCharacters K 𝒳) →
      ((y : ℤ) • (1 : G → K) ∈ inducedVirtualCharacters K 𝒳) →
      ((Nat.gcd x y : ℤ) • (1 : G → K) ∈ inducedVirtualCharacters K 𝒳) := by
    intro x y hx hy
    rw [Nat.gcd_eq_gcd_ab, add_smul]
    exact AddSubgroup.add_mem _ (by rw [mul_comm]; exact hmul _ _ hx)
      (by rw [mul_comm]; exact hmul _ _ hy)
  have hfin : ∀ s : Finset ℕ,
      (∀ q ∈ s, ((ordCompl[q] (Nat.card G) : ℕ) : ℤ) • (1 : G → K)
        ∈ inducedVirtualCharacters K 𝒳) →
      (((s.gcd fun q => ordCompl[q] (Nat.card G) : ℕ) : ℤ) • (1 : G → K)
        ∈ inducedVirtualCharacters K 𝒳) := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; rw [Finset.gcd_empty]; simp
    | insert q s _ ih =>
        intro h
        rw [Finset.gcd_insert]
        exact hgcd _ _ (h q (Finset.mem_insert_self q s))
          (ih fun r hr => h r (Finset.mem_insert_of_mem hr))
  -- the family `{ordCompl[q] |G|}` has gcd `1`
  have hgcd1 : (insert 2 (Nat.card G).primeFactors).gcd
      (fun q => ordCompl[q] (Nat.card G)) = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hdn : (insert 2 (Nat.card G).primeFactors).gcd
        (fun q => ordCompl[q] (Nat.card G)) ∣ Nat.card G :=
      (Finset.gcd_dvd (Finset.mem_insert_self 2 _)).trans (Nat.ordCompl_dvd _ 2)
    have hqmem : q ∈ (Nat.card G).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqd.trans hdn, hn0⟩
    exact Nat.not_dvd_ordCompl hq hn0
      (hqd.trans (Finset.gcd_dvd (Finset.mem_insert_of_mem hqmem)))
  have hprime : ∀ q ∈ insert 2 (Nat.card G).primeFactors, q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Nat.prime_two
    · exact Nat.prime_of_mem_primeFactors hq
  have hmem := hfin (insert 2 (Nat.card G).primeFactors) fun q hq =>
    zsmul_one_mem_inducedVirtualCharacters e h𝒳 hN hgN hωN (hprime q hq)
  rw [hgcd1] at hmem
  simpa using hmem

include e in
/-- **Gorenstein Lemma 7.10**: `v(G) = ch(G)`.  From `1_G ∈ v(G)` and the fact that `v(G)` is an
ideal of `ch(G)` (Lemma 7.3): every `θ ∈ ch(G)` is `1_G · θ`. -/
theorem inducedVirtualCharacters_eq_virtualCharacters (h𝒳 : IsElementaryFamily 𝒳) (hN : N ≠ 0)
    (hgN : ∀ g : G, g ^ N = 1) (hωN : IsPrimitiveRoot ω N) :
    inducedVirtualCharacters K 𝒳 = virtualCharacters K G :=
  le_antisymm (inducedVirtualCharacters_le_virtualCharacters e 𝒳) fun θ hθ => by
    simpa using
      mul_mem_inducedVirtualCharacters (one_mem_inducedVirtualCharacters e h𝒳 hN hgN hωN) hθ

/-! ### Brauer's characterization of characters -/

omit [CharZero K] [Finite ι'] [Invertible (Nat.card G : K)] in
/-- **The projection formula against a merely locally virtual class function.**  Lemma 7.3 with
`θ` only assumed to be a class function whose restriction to every `E ∈ 𝒳` is virtual: that is all
`induceFun_mul_restrict` needs, and it is exactly the hypothesis of Brauer's criterion. -/
theorem mul_mem_inducedVirtualCharacters_of_restrict {w θ : G → K}
    (hw : w ∈ inducedVirtualCharacters K 𝒳) (hcl : ∀ g h : G, θ (h * g * h⁻¹) = θ g)
    (hres : ∀ E ∈ 𝒳, θ ∘ E.subtype ∈ virtualCharacters K ↥E) :
    w * θ ∈ inducedVirtualCharacters K 𝒳 := by
  induction hw using AddSubgroup.closure_induction with
  | mem x hx =>
      obtain ⟨E, hE, ψ, hψ, rfl⟩ := hx
      rw [← induceFun_mul_restrict ψ hcl]
      exact induceFun_mem_inducedVirtualCharacters hE
        (mul_mem_virtualCharacters hψ (hres E hE))
  | zero => simpa only [zero_mul] using AddSubgroup.zero_mem _
  | add a b _ _ ha hb => simpa only [add_mul] using AddSubgroup.add_mem _ ha hb
  | neg a _ ha => simpa only [neg_mul] using AddSubgroup.neg_mem _ ha

include e in
/-- **Brauer's characterization of characters** (Brauer–Tate; Gorenstein Theorem 7.1).  A class
function on `G` whose restriction to every elementary subgroup is a virtual character is itself a
`ℤ`-combination of characters induced from elementary subgroups.

`θ = 1_G · θ` and `1_G ∈ v(G)`, so the projection formula moves `θ` inside the induction.  For the
classical form `θ ∈ ch(G)`, compose with `inducedVirtualCharacters_le_virtualCharacters`. -/
theorem mem_inducedVirtualCharacters_of_restrict (h𝒳 : IsElementaryFamily 𝒳) (hN : N ≠ 0)
    (hgN : ∀ g : G, g ^ N = 1) (hωN : IsPrimitiveRoot ω N) {θ : G → K}
    (hcl : ∀ g h : G, θ (h * g * h⁻¹) = θ g)
    (hres : ∀ E ∈ 𝒳, θ ∘ E.subtype ∈ virtualCharacters K ↥E) :
    θ ∈ inducedVirtualCharacters K 𝒳 := by
  simpa using mul_mem_inducedVirtualCharacters_of_restrict
    (one_mem_inducedVirtualCharacters e h𝒳 hN hgN hωN) hcl hres


end OddOrder.RepresentationTheory.Modular
