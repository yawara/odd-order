/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.QuadraticTraceCorrection

/-!
# An anisotropic `F`-bilinear cocycle on `𝐅_{q²}` is the Hermitian norm

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3 (4), p. 131 (and Appendix III, Proposition 1, p. 142).

Let `E = 𝐅_{q²}` have characteristic `2`, with `F = 𝐅_q` the fixed subfield of the
`q`-power Frobenius (`q = 2 ^ m`).  Chapter III §3 presents the group `Q` as a
twisted product `E × F` whose cocycle `φ` is `F`-bilinear (once `θ = 1`, which is
Chapter IV §3 (3)) and anisotropic, while Chapter IV §3 (4) works in the unitary
coordinates of `PSU(3, q)`, whose cocycle is the Hermitian one `x ȳ`.  Matching the
two presentations is exactly the statement that an anisotropic `F`-bilinear cocycle
has, after an `F`-linear change of the variable, the Hermitian norm `x ↦ x x̄` as its
diagonal — the characteristic-`2` case of "over a finite field there is only one
anisotropic binary quadratic form, the norm form of the quadratic extension".

The proof is the classical one, arranged so that no polynomial or field-extension
machinery is needed:

* the polar form `B` of `χ` is not identically zero (otherwise `x ↦ √(χ x)` would be
  an injection `E → F`);
* choosing `v` with `B v _ ≠ 0` and rescaling gives `w` with `B v w = χ v =: c`, and
  then `χ (a v + b w) = c (a² + a b + δ b²)` with `δ := χ w / c`;
* picking `u` with relative trace `1` gives `u^q = u + 1` and
  `(a + b u)(a + b u)^q = a² + a b + b² P` with `P := u² + u`;
* anisotropy says exactly that neither `δ` nor `P` is of the shape `t² + t`, and the
  Artin–Schreier map `t ↦ t² + t` of `F` has image of index `2`, so `δ + P = t² + t`
  is solvable — the substitution `a ↦ a + t b` turns one form into the other.

## Main results

* `OddOrder.FiniteField.artinSchreier` — the additive map `t ↦ t² + t`, and
  `add_mem_range_artinSchreier` — its image has index `2`.
* `OddOrder.FiniteField.frobCoordEquiv` — additive coordinates `F × F ≃+ E` attached
  to a pair of elements independent over `F`.
* `OddOrder.FiniteField.exists_addEquiv_norm_of_anisotropic_aux` — the classification,
  for a quadratic map given by its diagonal and polar form.
* `OddOrder.FiniteField.exists_addEquiv_norm_of_anisotropic` — the same for an
  `F`-bilinear anisotropic cocycle `φ`, the form in which Chapter III §3 delivers it.
-/

set_option autoImplicit false

namespace OddOrder.FiniteField

/-! ## The Artin–Schreier map of a field of characteristic two -/

section ArtinSchreier

variable (K : Type*) [Field K] [CharP K 2]

/-- **The Artin–Schreier map** `℘ : t ↦ t² + t` of a field of characteristic `2`.
It is additive because squaring is. -/
def artinSchreier : K →+ K :=
  AddMonoidHom.mk' (fun t => t ^ 2 + t) fun a b => by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (a * b) * h2

@[simp] theorem artinSchreier_apply (t : K) : artinSchreier K t = t ^ 2 + t := rfl

variable {K}

/-- `t² + t = 0` exactly for `t = 0` and `t = 1`: the two roots of `t (t + 1)`. -/
theorem artinSchreier_eq_zero_iff (t : K) : artinSchreier K t = 0 ↔ t = 0 ∨ t = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [artinSchreier_apply]
  constructor
  · intro h
    have hfac : t * (t + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by linear_combination h' - h2)
  · rintro (h | h) <;> rw [h]
    · ring
    · linear_combination h2

variable (K) in
/-- The kernel of `℘` is `{0, 1}`, of size `2`. -/
theorem natCard_ker_artinSchreier [Finite K] :
    Nat.card ↥(artinSchreier K).ker = 2 := by
  classical
  have hset : ((artinSchreier K).ker : Set K) = {0, 1} := by
    ext t
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    exact artinSchreier_eq_zero_iff t
  have h : Nat.card ↥(artinSchreier K).ker
      = Nat.card ↥(((artinSchreier K).ker : Set K)) := rfl
  rw [h, hset, Nat.card_coe_set_eq, Set.ncard_pair (zero_ne_one (α := K))]

variable (K) in
/-- **The image of the Artin–Schreier map has index `2`.**  Its kernel is `{0, 1}`, so
the image is half of `K`. -/
theorem index_range_artinSchreier [Finite K] : (artinSchreier K).range.index = 2 := by
  have hker : Nat.card ↥(artinSchreier K).ker * (artinSchreier K).ker.index
      = Nat.card K := AddSubgroup.card_mul_index _
  have hquot : (artinSchreier K).ker.index = Nat.card ↥(artinSchreier K).range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (artinSchreier K)).toEquiv
  have hrange : Nat.card ↥(artinSchreier K).range * (artinSchreier K).range.index
      = Nat.card K := AddSubgroup.card_mul_index _
  rw [natCard_ker_artinSchreier, hquot] at hker
  have hpos : 0 < Nat.card ↥(artinSchreier K).range := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [hrange, ← hker, Nat.mul_comm]

/-- **Two elements outside the image of `℘` differ by an element of the image**, the
only consequence of index `2` that is used. -/
theorem add_mem_range_artinSchreier [Finite K] {x y : K}
    (hx : x ∉ (artinSchreier K).range) (hy : y ∉ (artinSchreier K).range) :
    x + y ∈ (artinSchreier K).range :=
  (AddSubgroup.add_mem_iff_of_index_two (index_range_artinSchreier K)).mpr
    (by simp only [hx, hy, iff_self])

end ArtinSchreier

/-! ## Coordinates attached to an independent pair -/

section Coordinates

variable {E : Type*} [Field E] [Finite E] [CharP E 2] (m : ℕ)

/-- **Additive coordinates `F × F ≃+ E`** attached to a pair `v, w` of elements of
`E = 𝐅_{q²}` that is independent over `F = 𝐅_q`.  Bijectivity is injectivity plus
`|F|² = |E|`. -/
noncomputable def frobCoordEquiv (hm : m ≠ 0) (hcard : Nat.card E = (2 ^ m) ^ 2)
    {v w : E}
    (hind : ∀ a b : E, a ∈ frobFixedSubfield E 2 m → b ∈ frobFixedSubfield E 2 m →
      a * v + b * w = 0 → a = 0 ∧ b = 0) :
    (↥(frobFixedSubfield E 2 m) × ↥(frobFixedSubfield E 2 m)) ≃+ E :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun p => (p.1 : E) * v + (p.2 : E) * w) fun p p' => by
      simp only [Prod.fst_add, Prod.snd_add]
      push_cast
      ring)
    (by
      refine (Nat.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
      · rw [injective_iff_map_eq_zero]
        intro p hp
        obtain ⟨h1, h2⟩ := hind _ _ p.1.2 p.2.2 hp
        exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
      · rw [Nat.card_prod, natCard_frobFixedSubfield hcard hm, hcard, pow_two])

@[simp] theorem frobCoordEquiv_apply (hm : m ≠ 0) (hcard : Nat.card E = (2 ^ m) ^ 2)
    {v w : E}
    (hind : ∀ a b : E, a ∈ frobFixedSubfield E 2 m → b ∈ frobFixedSubfield E 2 m →
      a * v + b * w = 0 → a = 0 ∧ b = 0)
    (p : ↥(frobFixedSubfield E 2 m) × ↥(frobFixedSubfield E 2 m)) :
    frobCoordEquiv m hm hcard hind p = (p.1 : E) * v + (p.2 : E) * w :=
  rfl

end Coordinates

/-! ## The classification -/

section Classification

variable {E : Type*} [Field E] [Finite E] [CharP E 2] (m : ℕ)

/-- **An anisotropic `F`-quadratic map on `E = 𝐅_{q²}` is the Hermitian norm**, after
an `F`-linear change of variable.

The map is presented by its values `χ` together with its polar form `B`; the
hypotheses are exactly what an `F`-bilinear anisotropic cocycle supplies.  See
`exists_addEquiv_norm_of_anisotropic` for that packaging. -/
theorem exists_addEquiv_norm_of_anisotropic_aux (hm : m ≠ 0)
    (hcard : Nat.card E = (2 ^ m) ^ 2) (χ : E → E) (B : E → E → E)
    (hχmem : ∀ x : E, χ x ∈ frobFixedSubfield E 2 m)
    (hBmem : ∀ x y : E, B x y ∈ frobFixedSubfield E 2 m)
    (hχadd : ∀ x y : E, χ (x + y) = χ x + χ y + B x y)
    (hχsmul : ∀ a ∈ frobFixedSubfield E 2 m, ∀ x : E, χ (a * x) = a ^ 2 * χ x)
    (hBleft : ∀ a ∈ frobFixedSubfield E 2 m, ∀ x y : E, B (a * x) y = a * B x y)
    (hBright : ∀ a ∈ frobFixedSubfield E 2 m, ∀ x y : E, B x (a * y) = a * B x y)
    (hBself : ∀ x : E, B x x = 0)
    (haniso : ∀ x : E, x ≠ 0 → χ x ≠ 0) :
    ∃ f : E ≃+ E,
      (∀ a ∈ frobFixedSubfield E 2 m, ∀ x : E, f (a * x) = a * f x) ∧
      ∀ x : E, χ x = f x * f x ^ 2 ^ m := by
  classical
  letI : Algebra (ZMod 2) E := ZMod.algebra E 2
  have h2E : (2 : E) = 0 := CharTwo.two_eq_zero
  have hcancel : ∀ a b : E, a + b = 0 → a = b := fun a b h => by
    linear_combination h - b * h2E
  have hcardF : Nat.card ↥(frobFixedSubfield E 2 m) = 2 ^ m :=
    natCard_frobFixedSubfield hcard hm
  have hq2 : 2 ≤ 2 ^ m := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hm)
  have hsqinj : Function.Injective (fun z : E => z ^ 2) := by
    intro a b hab
    exact (frobeniusEquiv E 2).injective hab
  have hB0 : ∀ y : E, B 0 y = 0 := by
    intro y
    have h := hBleft 0 (zero_mem _) 0 y
    simpa using h
  -- ### the polar form is not identically zero
  obtain ⟨v, y₀, hBv⟩ : ∃ v y : E, B v y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hadd : ∀ x y : E, χ (x + y) = χ x + χ y := by
      intro x y
      rw [hχadd, hcon, add_zero]
    have hrsq : ∀ x : E, ((frobeniusEquiv E 2).symm (χ x)) ^ 2 = χ x := by
      intro x
      exact (frobeniusEquiv E 2).apply_symm_apply (χ x)
    have hrmem : ∀ x : E, (frobeniusEquiv E 2).symm (χ x) ∈ frobFixedSubfield E 2 m := by
      intro x
      rw [mem_frobFixedSubfield]
      apply hsqinj
      change (((frobeniusEquiv E 2).symm (χ x)) ^ 2 ^ m) ^ 2
        = ((frobeniusEquiv E 2).symm (χ x)) ^ 2
      rw [← pow_mul, mul_comm, pow_mul, hrsq]
      exact mem_frobFixedSubfield.mp (hχmem x)
    have hrinj : Function.Injective fun x : E => (frobeniusEquiv E 2).symm (χ x) := by
      intro x y hxy
      by_contra hne
      have hxy0 : x + y ≠ 0 := by
        intro h
        exact hne (hcancel _ _ h)
      refine haniso _ hxy0 ?_
      have hval : χ x = χ y := by
        have := congrArg (fun z : E => z ^ 2) hxy
        simpa only [hrsq] using this
      rw [hadd, hval]
      linear_combination (χ y) * h2E
    have hle : Nat.card E ≤ Nat.card ↥(frobFixedSubfield E 2 m) := by
      refine Nat.card_le_card_of_injective
        (fun x : E => (⟨(frobeniusEquiv E 2).symm (χ x), hrmem x⟩ :
          ↥(frobFixedSubfield E 2 m))) ?_
      intro x y hxy
      exact hrinj (congrArg Subtype.val hxy)
    rw [hcard, hcardF] at hle
    nlinarith [hq2]
  -- ### normalize the second basis vector
  have hvne : v ≠ 0 := by
    rintro rfl
    exact hBv (hB0 y₀)
  have hcmem : χ v ∈ frobFixedSubfield E 2 m := hχmem v
  have hcne : χ v ≠ 0 := haniso v hvne
  have hsmem : B v y₀ ∈ frobFixedSubfield E 2 m := hBmem v y₀
  have hcsmem : χ v * (B v y₀)⁻¹ ∈ frobFixedSubfield E 2 m :=
    Subfield.mul_mem _ hcmem (Subfield.inv_mem _ hsmem)
  set w : E := (χ v * (B v y₀)⁻¹) * y₀ with hwdef
  have hBvw : B v w = χ v := by
    rw [hwdef, hBright _ hcsmem, mul_assoc, inv_mul_cancel₀ hBv, mul_one]
  -- ### independence of `v` and `w`
  have hind : ∀ a b : E, a ∈ frobFixedSubfield E 2 m → b ∈ frobFixedSubfield E 2 m →
      a * v + b * w = 0 → a = 0 ∧ b = 0 := by
    intro a b ha hb hab
    by_cases hb0 : b = 0
    · subst hb0
      rw [zero_mul, add_zero] at hab
      rcases mul_eq_zero.mp hab with h | h
      · exact ⟨h, rfl⟩
      · exact absurd h hvne
    · exfalso
      have hbw : b * w = a * v := (hcancel _ _ hab).symm
      have hwv : w = (b⁻¹ * a) * v := by
        rw [mul_assoc, ← hbw, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
      refine hcne ?_
      rw [← hBvw, hwv, hBright _ (Subfield.mul_mem _ (Subfield.inv_mem _ hb) ha),
        hBself, mul_zero]
  -- ### the quadratic map in the coordinates `(a, b) ↦ a v + b w`
  have hdmem : χ w ∈ frobFixedSubfield E 2 m := hχmem w
  have hδmem : χ w * (χ v)⁻¹ ∈ frobFixedSubfield E 2 m :=
    Subfield.mul_mem _ hdmem (Subfield.inv_mem _ hcmem)
  have hquad : ∀ a b : E, a ∈ frobFixedSubfield E 2 m → b ∈ frobFixedSubfield E 2 m →
      χ (a * v + b * w) = a ^ 2 * χ v + a * b * χ v + b ^ 2 * χ w := by
    intro a b ha hb
    rw [hχadd, hχsmul a ha, hχsmul b hb, hBleft a ha, hBright b hb, hBvw]
    ring
  -- ### an element of relative trace one
  obtain ⟨u, hu⟩ := exists_frobTrace_eq_one (E := E) m hm hcard
  have huq : u ^ 2 ^ m = u + 1 := by
    rw [frobTrace_apply] at hu
    linear_combination hu - u * h2E
  have huF : u ∉ frobFixedSubfield E 2 m := by
    intro hmem
    have hfix : u ^ 2 ^ m = u := mem_frobFixedSubfield.mp hmem
    rw [hfix] at huq
    exact one_ne_zero (α := E) (by linear_combination -huq)
  have hPmem : u ^ 2 + u ∈ frobFixedSubfield E 2 m := by
    rw [mem_frobFixedSubfield, add_pow_char_pow, ← pow_mul, mul_comm 2 (2 ^ m),
      pow_mul, huq]
    linear_combination (u + 1) * h2E
  -- ### the norm form in the coordinates `(a, b) ↦ a + b u`
  have hnorm : ∀ a b : E, a ∈ frobFixedSubfield E 2 m → b ∈ frobFixedSubfield E 2 m →
      (a + b * u) * (a + b * u) ^ 2 ^ m = a ^ 2 + a * b + b ^ 2 * (u ^ 2 + u) := by
    intro a b ha hb
    have haq : a ^ 2 ^ m = a := mem_frobFixedSubfield.mp ha
    have hbq : b ^ 2 ^ m = b := mem_frobFixedSubfield.mp hb
    have hexp : (a + b * u) ^ 2 ^ m = a + b * (u + 1) := by
      rw [add_pow_char_pow, mul_pow, haq, hbq, huq]
    rw [hexp]
    linear_combination (a * b * u) * h2E
  -- ### neither invariant is an Artin–Schreier value
  haveI : CharP ↥(frobFixedSubfield E 2 m) 2 :=
    RingHom.charP (frobFixedSubfield E 2 m).subtype (RingHom.injective _) 2
  have hPnot : (⟨u ^ 2 + u, hPmem⟩ : ↥(frobFixedSubfield E 2 m)) ∉
      (artinSchreier ↥(frobFixedSubfield E 2 m)).range := by
    rintro ⟨t, ht⟩
    have hval : (t : E) ^ 2 + (t : E) = u ^ 2 + u := congrArg Subtype.val ht
    have hfac : (u + (t : E)) * (u + (t : E) + 1) = 0 := by
      linear_combination hval + (u ^ 2 + u * (t : E) + u) * h2E
    have hmem : u ∈ frobFixedSubfield E 2 m := by
      rcases mul_eq_zero.mp hfac with h | h
      · have : u = (t : E) := hcancel _ _ h
        rw [this]
        exact t.2
      · have : u = (t : E) + 1 := by
          refine hcancel _ _ ?_
          linear_combination h
        rw [this]
        exact Subfield.add_mem _ t.2 (one_mem _)
    exact huF hmem
  have hδnot : (⟨χ w * (χ v)⁻¹, hδmem⟩ : ↥(frobFixedSubfield E 2 m)) ∉
      (artinSchreier ↥(frobFixedSubfield E 2 m)).range := by
    rintro ⟨t, ht⟩
    have hval : (t : E) ^ 2 + (t : E) = χ w * (χ v)⁻¹ := congrArg Subtype.val ht
    have hne : (t : E) * v + 1 * w ≠ 0 := by
      intro h
      exact one_ne_zero (hind _ _ t.2 (one_mem _) h).2
    have hvalw : χ v * ((t : E) ^ 2 + (t : E)) = χ w := by
      rw [hval]
      field_simp
    refine haniso _ hne ?_
    rw [hquad _ _ t.2 (one_mem _)]
    linear_combination hvalw + χ w * h2E
  obtain ⟨t, ht⟩ := add_mem_range_artinSchreier hδnot hPnot
  have htval : (t : E) ^ 2 + (t : E) = χ w * (χ v)⁻¹ + (u ^ 2 + u) :=
    congrArg Subtype.val ht
  -- ### the square root of the leading coefficient
  obtain ⟨e, he⟩ := (frobeniusEquiv ↥(frobFixedSubfield E 2 m) 2).surjective
    (⟨χ v, hcmem⟩ : ↥(frobFixedSubfield E 2 m))
  have heval : (e : E) ^ 2 = χ v := congrArg Subtype.val he
  have hene : (e : E) ≠ 0 := by
    intro h
    exact hcne (by rw [← heval, h]; ring)
  have htval2 : (e : E) ^ 2 * ((t : E) ^ 2 + (t : E))
      = χ w + (e : E) ^ 2 * (u ^ 2 + u) := by
    rw [heval, htval]
    field_simp
  -- ### the second coordinate system
  have hind2 : ∀ a b : E, a ∈ frobFixedSubfield E 2 m → b ∈ frobFixedSubfield E 2 m →
      a * (e : E) + b * ((e : E) * ((t : E) + u)) = 0 → a = 0 ∧ b = 0 := by
    intro a b ha hb hab
    have hfac : (e : E) * (a + b * (t : E) + b * u) = 0 := by linear_combination hab
    have hzero : a + b * (t : E) + b * u = 0 :=
      (mul_eq_zero.mp hfac).resolve_left hene
    by_cases hb0 : b = 0
    · subst hb0
      refine ⟨?_, rfl⟩
      simpa using hzero
    · exfalso
      have hbu : b * u = a + b * (t : E) := (hcancel _ _ hzero).symm
      have hueq : u = b⁻¹ * (a + b * (t : E)) := by
        rw [← hbu, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
      refine huF ?_
      rw [hueq]
      exact Subfield.mul_mem _ (Subfield.inv_mem _ hb)
        (Subfield.add_mem _ ha (Subfield.mul_mem _ hb t.2))
  set g := frobCoordEquiv m hm hcard hind with hgdef
  set h := frobCoordEquiv m hm hcard hind2 with hhdef
  refine ⟨g.symm.trans h, ?_, ?_⟩
  · -- `F`-linearity
    intro a ha x
    obtain ⟨p, rfl⟩ := g.surjective x
    have hax : a * g p = g (⟨a * (p.1 : E), Subfield.mul_mem _ ha p.1.2⟩,
        ⟨a * (p.2 : E), Subfield.mul_mem _ ha p.2.2⟩) := by
      rw [hgdef]
      simp only [frobCoordEquiv_apply]
      ring
    simp only [AddEquiv.trans_apply, hax, AddEquiv.symm_apply_apply, hhdef,
      frobCoordEquiv_apply]
    ring
  · -- the diagonal is the norm
    intro x
    obtain ⟨p, rfl⟩ := g.surjective x
    have hfval : (g.symm.trans h) (g p)
        = (p.1 : E) * (e : E) + (p.2 : E) * ((e : E) * ((t : E) + u)) := by
      simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply, hhdef,
        frobCoordEquiv_apply]
    have hxval : χ (g p)
        = (p.1 : E) ^ 2 * χ v + (p.1 : E) * (p.2 : E) * χ v
          + (p.2 : E) ^ 2 * χ w := by
      have hgp : g p = (p.1 : E) * v + (p.2 : E) * w := rfl
      rw [hgp, hquad _ _ p.1.2 p.2.2]
    have heq : (e : E) ^ 2 ^ m = (e : E) := mem_frobFixedSubfield.mp e.2
    have habmem : (p.1 : E) + (t : E) * (p.2 : E) ∈ frobFixedSubfield E 2 m :=
      Subfield.add_mem _ p.1.2 (Subfield.mul_mem _ t.2 p.2.2)
    -- the value is `e · ((a + t b) + b u)`, so its norm is `e² · N(a + t b + b u)`
    have hRHS : ((p.1 : E) * (e : E) + (p.2 : E) * ((e : E) * ((t : E) + u)))
          * ((p.1 : E) * (e : E) + (p.2 : E) * ((e : E) * ((t : E) + u))) ^ 2 ^ m
        = (e : E) ^ 2 * ((((p.1 : E) + (t : E) * (p.2 : E)) + (p.2 : E) * u)
            * (((p.1 : E) + (t : E) * (p.2 : E)) + (p.2 : E) * u) ^ 2 ^ m) := by
      have hsplit : (p.1 : E) * (e : E) + (p.2 : E) * ((e : E) * ((t : E) + u))
          = (e : E) * (((p.1 : E) + (t : E) * (p.2 : E)) + (p.2 : E) * u) := by ring
      rw [hsplit, mul_pow, heq]
      ring
    rw [hxval, hfval, hRHS, hnorm _ _ habmem p.2.2, ← heval]
    linear_combination (-((p.2 : E) ^ 2)) * htval2
      - ((e : E) ^ 2 * (p.2 : E) ^ 2 * (u ^ 2 + u)
        + (e : E) ^ 2 * (t : E) * (p.1 : E) * (p.2 : E)) * h2E

/-- **Chapter III §3's cocycle is the Hermitian one**, up to an `F`-linear change of
variable: an anisotropic `F`-bilinear `φ : E × E → F` on `E = 𝐅_{q²}` has
`φ (f x) (f x) = x x̄` for an additive (indeed `F`-linear) bijection `f`.

The `F`-bilinearity hypothesis is the `θ = 1` case of the semilinearity
`φ (a x) (b y) = a b^θ φ x y` supplied by the Proposition of Peterfalvi Part II,
Ch. III §3 (p. 120); `θ = 1` is Chapter IV §3 (3). -/
theorem exists_addEquiv_norm_of_anisotropic (hm : m ≠ 0)
    (hcard : Nat.card E = (2 ^ m) ^ 2) [Algebra (ZMod 2) E]
    (φ : LinearMap.BilinMap (ZMod 2) E ↥(frobFixedSubfield E 2 m))
    (hsemi : ∀ a ∈ frobFixedSubfield E 2 m, ∀ b ∈ frobFixedSubfield E 2 m, ∀ x y : E,
      ((φ (a * x) (b * y) : ↥(frobFixedSubfield E 2 m)) : E)
        = a * b * ((φ x y : ↥(frobFixedSubfield E 2 m)) : E))
    (haniso : ∀ x : E, x ≠ 0 → φ x x ≠ 0) :
    ∃ f : E ≃+ E,
      (∀ a ∈ frobFixedSubfield E 2 m, ∀ x : E, f (a * x) = a * f x) ∧
      ∀ x : E, ((φ x x : ↥(frobFixedSubfield E 2 m)) : E) = f x * f x ^ 2 ^ m := by
  refine exists_addEquiv_norm_of_anisotropic_aux m hm hcard
    (fun x => ((φ x x : ↥(frobFixedSubfield E 2 m)) : E))
    (fun x y => ((φ x y : ↥(frobFixedSubfield E 2 m)) : E)
      + ((φ y x : ↥(frobFixedSubfield E 2 m)) : E))
    (fun x => (φ x x).2) (fun x y => Subfield.add_mem _ (φ x y).2 (φ y x).2)
    ?_ ?_ ?_ ?_ (fun x => CharTwo.add_self_eq_zero _) ?_
  · -- the polar form is the defect of additivity of the diagonal
    intro x y
    have h : φ (x + y) (x + y) = φ x x + φ x y + (φ y x + φ y y) := by
      simp only [map_add, LinearMap.add_apply]
      abel
    rw [h]
    push_cast
    ring
  · -- the diagonal scales by the square
    intro a ha x
    have h := hsemi a ha a ha x x
    rw [h]
    ring
  · -- left `F`-linearity of the polar form
    intro a ha x y
    have h1 := hsemi a ha 1 (one_mem _) x y
    have h2 := hsemi 1 (one_mem _) a ha y x
    rw [one_mul] at h1 h2
    rw [h1, h2]
    ring
  · -- right `F`-linearity of the polar form
    intro a ha x y
    have h1 := hsemi 1 (one_mem _) a ha x y
    have h2 := hsemi a ha 1 (one_mem _) y x
    rw [one_mul] at h1 h2
    rw [h1, h2]
    ring
  · -- anisotropy, transported through the coercion
    intro x hx h0
    exact haniso x hx (Subtype.ext h0)

end Classification

end OddOrder.FiniteField
