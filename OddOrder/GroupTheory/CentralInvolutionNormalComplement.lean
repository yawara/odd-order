/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Basic

/-!
# A group of order-`4` Sylow `2`-subgroup with a central involution has a normal `2`-complement

This is the step Navarro takes inside the proof of (7.2):

> "First, notice that `C` cannot have a unique class of involutions (because `t` is central in `C`).
> By the first part applied to `C`, we conclude that `C` has three classes of involutions and,
> therefore, that `C` has a normal `2`-complement."

The "first part" is Burnside's normal `p`-complement theorem applied after checking
`N_H(V) = C_H(V)`, and that check is what this file does.  Writing `V = {1, v, a, va}` for the
Sylow `2`-subgroup (any group of order `4` has this shape once `v` is an involution in it),
conjugation by `n ∈ N_H(V)` fixes `v` — it is central — hence sends `a` to `a` or to `va`.  In the
first case `n` centralises `V`; in the second, `n²` does, because `v² = 1`.  So the index
`[N_H(V) : C_H(V)]` has exponent `2`; but `V ≤ C_H(V)` and `V` is Sylow, so that index is odd.
An odd number dividing a power of `2` is `1`.

Note that `V` is *not* assumed to be Klein four: the argument runs verbatim for the cyclic group of
order `4` (whose unique involution is central in it), which is why the hypothesis is only
`|V| = 4` together with an involution of `V` central in `H`.

## Main results

* `OddOrder.GroupTheory.normalizer_le_centralizer_of_card_four_of_central_involution`
* `OddOrder.GroupTheory.hasNormalPComplement_of_card_four_of_central_involution`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, proof of (7.2), p. 132.
* I. M. Isaacs, *Finite Group Theory*, Thm 5.13 (Burnside).
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch05

variable {H : Type*} [Group H] [Finite H]

/-- **`V = {1, v, a, va}`** for a subgroup of order `4` containing an involution `v` and an
element `a ∉ {1, v}`. -/
theorem eq_or_eq_or_eq_or_eq_of_card_four {P : Subgroup H} (hcard : Nat.card ↥P = 4)
    {v a : H} (hvP : v ∈ P) (haP : a ∈ P) (hv1 : v ≠ 1) (hv2 : v * v = 1) (ha1 : a ≠ 1)
    (hav : a ≠ v) {u : H} (hu : u ∈ P) :
    u = 1 ∨ u = v ∨ u = a ∨ u = v * a := by
  classical
  have : Fintype ↥P := Fintype.ofFinite _
  have h4 : Fintype.card ↥P = 4 := by rw [← Nat.card_eq_fintype_card, hcard]
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  -- the four listed elements are distinct
  have hva1 : v * a ≠ 1 := fun h => hav (by
    have h2 : v⁻¹ * (v * a) = v⁻¹ * 1 := by rw [h]
    rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h2
    rw [h2, hvinv])
  have hvav : v * a ≠ v := fun h => ha1 (by
    have h2 : v⁻¹ * (v * a) = v⁻¹ * v := by rw [h]
    rw [← mul_assoc, inv_mul_cancel, one_mul] at h2
    exact h2)
  have hvaa : v * a ≠ a := fun h => hv1 (by
    have h2 : v * a * a⁻¹ = a * a⁻¹ := by rw [h]
    rw [mul_assoc, mul_inv_cancel, mul_one] at h2
    exact h2)
  set S : Finset ↥P :=
    {⟨1, one_mem P⟩, ⟨v, hvP⟩, ⟨a, haP⟩, ⟨v * a, mul_mem hvP haP⟩} with hS
  have hcardS : S.card = 4 := by
    rw [hS]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
        push Not
        exact ⟨fun h => hv1 h.symm, fun h => ha1 h.symm, fun h => hva1 h.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
        push Not
        exact ⟨fun h => hav h.symm, fun h => hvav h.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton, Subtype.mk.injEq]
        exact fun h => hvaa h.symm),
      Finset.card_singleton]
  have huniv : S = Finset.univ := Finset.eq_univ_of_card _ (by rw [hcardS, h4])
  have hmem : (⟨u, hu⟩ : ↥P) ∈ S := huniv ▸ Finset.mem_univ _
  rw [hS] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq] at hmem
  exact hmem

/-- **Burnside's criterion is met**: for a Sylow `2`-subgroup `V` of order `4` containing an
involution `v` that is central in `H`, the normaliser of `V` centralises it. -/
theorem normalizer_le_centralizer_of_card_four_of_central_involution
    (V : Sylow 2 H) (hcard : Nat.card ↥(V : Subgroup H) = 4)
    {v : H} (hvV : v ∈ (V : Subgroup H)) (hv1 : v ≠ 1) (hv2 : v * v = 1)
    (hvZ : ∀ h : H, h * v = v * h) :
    Subgroup.normalizer ((V : Subgroup H) : Set H)
      ≤ Subgroup.centralizer ((V : Subgroup H) : Set H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥(V : Subgroup H) := Fintype.ofFinite _
  -- an element of `V` outside `{1, v}`
  obtain ⟨a, haV, ha1, hav⟩ : ∃ a ∈ (V : Subgroup H), a ≠ 1 ∧ a ≠ v := by
    by_contra hc
    push Not at hc
    have hsub : (Finset.univ : Finset ↥(V : Subgroup H))
        ⊆ {⟨1, one_mem _⟩, ⟨v, hvV⟩} := by
      intro u _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases eq_or_ne (u : H) 1 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext (hc (u : H) u.2 h))
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at h1
    have h2 : ({⟨1, one_mem (V : Subgroup H)⟩, ⟨v, hvV⟩} :
        Finset ↥(V : Subgroup H)).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])
    omega
  have henum : ∀ u ∈ (V : Subgroup H), u = 1 ∨ u = v ∨ u = a ∨ u = v * a := fun u hu =>
    eq_or_eq_or_eq_or_eq_of_card_four hcard hvV haV hv1 hv2 ha1 hav hu
  -- `V` is abelian, so `V ≤ C_H(V)`
  have hvC : v ∈ Subgroup.centralizer ((V : Subgroup H) : Set H) :=
    Subgroup.mem_centralizer_iff.mpr fun u _ => hvZ u
  have haC : a ∈ Subgroup.centralizer ((V : Subgroup H) : Set H) := by
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    rcases henum u hu with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact (hvZ a).symm
    · rfl
    · rw [← mul_assoc, hvZ a]
  have hVC : (V : Subgroup H) ≤ Subgroup.centralizer ((V : Subgroup H) : Set H) := by
    intro u hu
    rcases henum u hu with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hvC
    · exact haC
    · exact mul_mem hvC haC
  -- conjugation by a normalising element fixes `v` and moves `a` inside `{a, va}`
  have hconj : ∀ n ∈ Subgroup.normalizer ((V : Subgroup H) : Set H), ∀ u ∈ (V : Subgroup H),
      n * u * n⁻¹ ∈ (V : Subgroup H) := fun n hn u hu =>
    (Subgroup.mem_normalizer_iff.mp hn u).mp hu
  have hconj' : ∀ n ∈ Subgroup.normalizer ((V : Subgroup H) : Set H), ∀ u ∈ (V : Subgroup H),
      n⁻¹ * u * n ∈ (V : Subgroup H) := by
    intro n hn u hu
    refine (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * u * n)).mpr ?_
    have : n * (n⁻¹ * u * n) * n⁻¹ = u := by group
    rw [this]
    exact hu
  have hfixv : ∀ n : H, n * v * n⁻¹ = v := fun n => by
    rw [hvZ n, mul_assoc, mul_inv_cancel, mul_one]
  -- squares of normalising elements centralise `V`
  have hsq : ∀ n ∈ Subgroup.normalizer ((V : Subgroup H) : Set H),
      n * n ∈ Subgroup.centralizer ((V : Subgroup H) : Set H) := by
    intro n hn
    -- `σ u = n u n⁻¹` satisfies `σ (σ u) = u` on `V`
    have hcase : n * a * n⁻¹ = a ∨ n * a * n⁻¹ = v * a := by
      rcases henum _ (hconj n hn a haV) with h | h | h | h
      · exact absurd (by
          have : a = n⁻¹ * 1 * n := by rw [← h]; group
          rw [this]; group) ha1
      · refine absurd ?_ hav
        have h2 : n * a * n⁻¹ = n * v * n⁻¹ := by rw [h, hfixv n]
        have := mul_right_cancel (b := n⁻¹) h2
        exact mul_left_cancel this
      · exact Or.inl h
      · exact Or.inr h
    have hsigma : ∀ u ∈ (V : Subgroup H), n * (n * u * n⁻¹) * n⁻¹ = u := by
      have hva : n * (n * a * n⁻¹) * n⁻¹ = a := by
        rcases hcase with h | h
        · rw [h, h]
        · rw [h]
          have hstep : n * (v * a) * n⁻¹ = (n * v * n⁻¹) * (n * a * n⁻¹) := by group
          rw [hstep, hfixv n, h, ← mul_assoc, hv2, one_mul]
      intro u hu
      rcases henum u hu with rfl | rfl | rfl | rfl
      · group
      · rw [hfixv n, hfixv n]
      · exact hva
      · have hstep : n * (v * a) * n⁻¹ = (n * v * n⁻¹) * (n * a * n⁻¹) := by group
        rw [hstep, hfixv n]
        have hstep2 : n * (v * (n * a * n⁻¹)) * n⁻¹
            = (n * v * n⁻¹) * (n * (n * a * n⁻¹) * n⁻¹) := by group
        rw [hstep2, hfixv n, hva]
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have h := hsigma u hu
    have : n * n * u * (n * n)⁻¹ = u := by
      rw [show n * n * u * (n * n)⁻¹ = n * (n * u * n⁻¹) * n⁻¹ by group]
      exact h
    calc u * (n * n) = (n * n * u * (n * n)⁻¹) * (n * n) := by rw [this]
      _ = n * n * u := by group
  -- the index of `C_H(V)` in `N_H(V)` is odd and kills squares, hence trivial
  set NN : Subgroup H := Subgroup.normalizer ((V : Subgroup H) : Set H) with hNN
  set CC : Subgroup H := Subgroup.centralizer ((V : Subgroup H) : Set H) with hCC
  have hCNN : CC ≤ NN := by
    intro c hc
    refine Subgroup.mem_normalizer_iff.mpr fun u => ?_
    have hcu : ∀ w ∈ (V : Subgroup H), c * w * c⁻¹ = w := fun w hw => by
      rw [← Subgroup.mem_centralizer_iff.mp hc w hw, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · rw [hcu u hu]; exact hu
    · have hback : u = c⁻¹ * (c * u * c⁻¹) * c := by group
      have hstep : c⁻¹ * (c * u * c⁻¹) * c = c * u * c⁻¹ := by
        rw [mul_assoc, Subgroup.mem_centralizer_iff.mp hc _ hu, ← mul_assoc, inv_mul_cancel,
          one_mul]
      rw [hback, hstep]
      exact hu
  set D : Subgroup ↥NN := CC.subgroupOf NN with hD
  have hDnorm : D.Normal := by
    constructor
    intro d hd n
    rw [hD, Subgroup.mem_subgroupOf] at hd ⊢
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have hnu : (n : H)⁻¹ * u * (n : H) ∈ (V : Subgroup H) := hconj' (n : H) n.2 u hu
    have hdc := Subgroup.mem_centralizer_iff.mp hd _ hnu
    have key : (n : H) * (d : H) * (n : H)⁻¹ * u * ((n : H) * (d : H) * (n : H)⁻¹)⁻¹ = u := by
      have : (n : H) * (d : H) * (n : H)⁻¹ * u * ((n : H) * (d : H) * (n : H)⁻¹)⁻¹
          = (n : H) * ((d : H) * ((n : H)⁻¹ * u * (n : H)) * (d : H)⁻¹) * (n : H)⁻¹ := by group
      rw [this, show (d : H) * ((n : H)⁻¹ * u * (n : H)) * (d : H)⁻¹
          = ((n : H)⁻¹ * u * (n : H)) by
        rw [← hdc, mul_assoc, mul_inv_cancel, mul_one]]
      group
    calc u * ((n : H) * (d : H) * (n : H)⁻¹)
        = ((n : H) * (d : H) * (n : H)⁻¹ * u * ((n : H) * (d : H) * (n : H)⁻¹)⁻¹)
            * ((n : H) * (d : H) * (n : H)⁻¹) := by rw [key]
      _ = (n : H) * (d : H) * (n : H)⁻¹ * u := by group
  -- odd index
  have hoddindex : ¬ 2 ∣ D.index := by
    have hVNN : (V : Subgroup H) ≤ NN := by rw [hNN]; exact Subgroup.le_normalizer
    have hle : (V : Subgroup H).subgroupOf NN ≤ D := by
      intro u hu
      rw [hD, Subgroup.mem_subgroupOf]
      exact hVC (Subgroup.mem_subgroupOf.mp hu)
    have hdvd : D.index ∣ ((V : Subgroup H).subgroupOf NN).index :=
      Subgroup.index_dvd_of_le hle
    exact fun h2 => (V.subtype hVNN).not_dvd_index (h2.trans hdvd)
  -- an element of odd order squaring to `1` is trivial
  intro n hn
  have hnD : (⟨n, hn⟩ : ↥NN) ∈ D := by
    have : Finite ↥NN := Subtype.finite
    set q : ↥NN ⧸ D := QuotientGroup.mk ⟨n, hn⟩ with hq
    have hq2 : q ^ 2 = 1 := by
      rw [hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hD, Subgroup.mem_subgroupOf]
      have hcoe : (((⟨n, hn⟩ : ↥NN) ^ 2 : ↥NN) : H) = n * n := by rw [sq]; rfl
      rw [hcoe]
      exact hsq n hn
    have h1 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
    have h2 : orderOf q ∣ Nat.card (↥NN ⧸ D) := orderOf_dvd_natCard _
    have h3 : Nat.card (↥NN ⧸ D) = D.index := rfl
    have h4 : orderOf q = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · exact absurd (h ▸ (h3 ▸ h2)) hoddindex
    have := orderOf_eq_one_iff.mp h4
    rwa [hq, QuotientGroup.eq_one_iff] at this
  rw [hD, Subgroup.mem_subgroupOf] at hnD
  exact hnD

/-- **Navarro's step inside (7.2)**: a finite group whose Sylow `2`-subgroup has order `4` and
contains a central involution has a normal `2`-complement.

In Navarro's application `H = C_G(t)` for `t` an involution of a Klein four Sylow `2`-subgroup:
`t` is central in `H` and the Sylow `2`-subgroup of `H` is still the Klein four group. -/
theorem hasNormalPComplement_of_card_four_of_central_involution
    (V : Sylow 2 H) (hcard : Nat.card ↥(V : Subgroup H) = 4)
    {v : H} (hvV : v ∈ (V : Subgroup H)) (hv1 : v ≠ 1) (hv2 : v * v = 1)
    (hvZ : ∀ h : H, h * v = v * h) :
    HasNormalPComplement 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hasNormalPComplement_of_sylow_normalizer_le_centralizer V
    (normalizer_le_centralizer_of_card_four_of_central_involution V hcard hvV hv1 hv2 hvZ)

/-- **The Sylow `2`-subgroups of `C_Q(y)` still have order `4`** when those of `Q` do and `y` is
an involution.

An involution lies in *some* Sylow `2`-subgroup `S'`, which is abelian (order `p²`), so
`S' ≤ C_Q(y)`; being Sylow in `Q` it is Sylow in `C_Q(y)`, and all Sylow `2`-subgroups of
`C_Q(y)` are conjugate to it. -/
theorem card_sylow_centralizer_of_card_sylow_four {Q : Type*} [Group Q] [Finite Q]
    (S : Sylow 2 Q) (hcard : Nat.card ↥(S : Subgroup Q) = 4)
    {y : Q} (hy1 : y ≠ 1) (hy2 : y * y = 1)
    (V : Sylow 2 ↥(Subgroup.centralizer ({y} : Set Q))) :
    Nat.card ↥(V : Subgroup ↥(Subgroup.centralizer ({y} : Set Q))) = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hyp : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨S', hS'⟩ := hyp.exists_le_sylow
  have hcard' : Nat.card ↥(S' : Subgroup Q) = 4 := by
    rw [← hcard]
    exact Nat.card_congr (Sylow.equiv S' S).toEquiv
  have hcomm : ∀ a b : ↥(S' : Subgroup Q), a * b = b * a :=
    isMulCommutative_iff.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hcard']; norm_num))
  have hyS' : y ∈ (S' : Subgroup Q) := hS' (Subgroup.mem_zpowers y)
  have hle : (S' : Subgroup Q) ≤ Subgroup.centralizer ({y} : Set Q) := by
    intro u hu
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact congrArg Subtype.val (hcomm (⟨w, hyS'⟩ : ↥(S' : Subgroup Q)) ⟨u, hu⟩)
  have hVcard : Nat.card ↥((S'.subtype hle : Sylow 2 ↥(Subgroup.centralizer ({y} : Set Q)))
      : Subgroup ↥(Subgroup.centralizer ({y} : Set Q))) = 4 := by
    rw [Sylow.coe_subtype, ← hcard']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [← hVcard]
  exact Nat.card_congr (Sylow.equiv V (S'.subtype hle)).toEquiv

/-- **Navarro (7.2) applied to a centraliser**: if the Sylow `2`-subgroups of `Q` have order `4`,
then the centraliser of any involution of `Q` has a normal `2`-complement.

This is the form the Brauer–Suzuki chain consumes: `Q = C_G(t)/⟨t⟩` has Klein four Sylow
`2`-subgroups (the image of a quaternion `Q₈`), and `ȳ` is one of its involutions. -/
theorem hasNormalPComplement_centralizer_of_card_sylow_four {Q : Type*} [Group Q] [Finite Q]
    (S : Sylow 2 Q) (hcard : Nat.card ↥(S : Subgroup Q) = 4)
    {y : Q} (hy1 : y ≠ 1) (hy2 : y * y = 1) :
    HasNormalPComplement 2 ↥(Subgroup.centralizer ({y} : Set Q)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyC : y ∈ Subgroup.centralizer ({y} : Set Q) :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff] at hw; subst hw; rfl
  -- `y` lies in some Sylow `2`-subgroup of its centraliser, and that has order `4`
  have hord : orderOf (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({y} : Set Q))) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hy2)
      (fun h => hy1 (congrArg Subtype.val h))
  have hyp : IsPGroup 2 ↥(Subgroup.zpowers (⟨y, hyC⟩ :
      ↥(Subgroup.centralizer ({y} : Set Q)))) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨V, hV⟩ := hyp.exists_le_sylow
  refine hasNormalPComplement_of_card_four_of_central_involution V
    (card_sylow_centralizer_of_card_sylow_four S hcard hy1 hy2 V) (v := ⟨y, hyC⟩)
    (hV (Subgroup.mem_zpowers _)) (fun h => hy1 (congrArg Subtype.val h)) (Subtype.ext hy2) ?_
  intro h
  refine Subtype.ext ?_
  exact (Subgroup.mem_centralizer_iff.mp h.2 y (Set.mem_singleton y)).symm

/-- **Unpacking a normal `p`-complement** into the shape the block-theoretic chain asks for: a
normal `p'`-subgroup `M` of index a power of `p`.

`M.index = |P|` for a Sylow `p`-subgroup `P` (they are complements), and `|M| = P.index` is prime
to `p`.  The index form avoids having to carry the `Normal` instance inside the statement; the
consumer turns it into `IsPGroup p (H ⧸ M)` with `IsPGroup.of_card`. -/
theorem exists_normal_of_hasNormalPComplement {p : ℕ} [Fact p.Prime]
    (h : HasNormalPComplement p H) :
    ∃ M : Subgroup H, M.Normal ∧ ¬ p ∣ Nat.card ↥M ∧ ∃ n : ℕ, M.index = p ^ n := by
  classical
  obtain ⟨M, hMnorm, hcompl⟩ := h
  obtain ⟨P⟩ : Nonempty (Sylow p H) := Sylow.nonempty
  refine ⟨M, hMnorm, ?_, ?_⟩
  · rw [← (hcompl P).index_eq_card]
    exact P.not_dvd_index
  · obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact ⟨n, by rw [← hn]; exact (hcompl P).symm.index_eq_card⟩

end OddOrder.GroupTheory
