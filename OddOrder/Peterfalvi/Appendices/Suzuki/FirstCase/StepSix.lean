/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepFive

/-!
# Peterfalvi Part II, Ch. II, step (6): the arithmetic lemma

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (6), p. 110.

Step (6) rests on a number-theoretic lemma quoted from Huppert–Blackburn
([HB], Kapitel IX, Lemma 2.7): the only way an odd prime power `f^a` can equal
`2^b + 1` is `a = 1` (so `f = 2^b + 1` is a Fermat prime) or `f^a = 9`
(`3² = 2³ + 1`).

This leaf formalizes that lemma as `eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one`
(pure `ℕ` arithmetic, axiom-clean).  The elementary proof:

* if `a ≥ 2`, the geometric sum `S = ∑_{i<a} f^i` divides `2^b` (as
  `(f - 1) · S = f^a - 1 = 2^b`), so `S` is a power of `2`; but `S ≡ a (mod 2)`
  (each `f^i` is odd), and `S ≥ 1 + f ≥ 4` is even, forcing `a` even;
* writing `a = 2c`, `(f^c - 1)(f^c + 1) = 2^b`, so both factors are powers of
  `2` differing by `2`, hence `2` and `4`; thus `f^c = 3` and `f^a = 9`.

The lemma is consumed by step (6) (`|F| = f^a = 2^b + 1`) and step (8)
(`|C_F(w)| = f^a = 2^b + 1`).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

/-- **[HB] Kapitel IX, Lemma 2.7** (arithmetic): if `f` is odd and
`f ^ a = 2 ^ b + 1` with `b ≥ 1`, then `a = 1` or `f ^ a = 9`.

Consumed by step (6) and step (8) of Peterfalvi Part II, Ch. II. -/
theorem eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one {f a b : ℕ}
    (hf : Odd f) (hb : 1 ≤ b) (h : f ^ a = 2 ^ b + 1) :
    a = 1 ∨ f ^ a = 9 := by
  have hfodd := Nat.odd_iff.mp hf
  have hb2 : 2 ≤ 2 ^ b := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  -- `f ≥ 3`
  have hf3 : 3 ≤ f := by
    rcases Nat.lt_or_ge f 3 with hlt | hge
    · exfalso
      have hf1 : f = 1 := by omega
      rw [hf1, one_pow] at h
      omega
    · exact hge
  -- `a ≥ 1`
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [pow_zero] at h; omega
    · exact hpos
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · left; omega
  right
  -- `a ≥ 2`.  The geometric sum `S = ∑_{i<a} f^i`.
  set S : ℕ := ∑ i ∈ Finset.range a, f ^ i with hSdef
  -- `(f - 1) · S = f^a - 1 = 2^b`
  have hgeom : (f - 1) * S = f ^ a - 1 := by
    rw [hSdef, Nat.geomSum_eq (by omega) a]
    exact Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one f a)
  have hprod : (f - 1) * S = 2 ^ b := by rw [hgeom]; omega
  have hSdvd : S ∣ 2 ^ b := ⟨f - 1, by rw [← hprod]; ring⟩
  obtain ⟨k, -, hSk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hSdvd
  -- `S ≡ a (mod 2)`
  have hSpar : S % 2 = a % 2 := by
    rw [hSdef, Finset.sum_nat_mod]
    have hone : ∀ i ∈ Finset.range a, f ^ i % 2 = 1 :=
      fun i _ => Nat.odd_iff.mp hf.pow
    rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
  -- `S ≥ 1 + f ≥ 4`, so `S` is even, hence `a` is even
  have hSge : 4 ≤ S := by
    have hsub : Finset.range 2 ⊆ Finset.range a := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    have hle : ∑ i ∈ Finset.range 2, f ^ i ≤ S :=
      hSdef ▸ Finset.sum_le_sum_of_subset hsub
    have h2 : ∑ i ∈ Finset.range 2, f ^ i = 1 + f := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]; ring
    rw [h2] at hle; omega
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_zero] at hSk; omega
    · exact hkpos
  have hSeven : 2 ∣ S := hSk ▸ dvd_pow_self 2 (by omega)
  have haeven : 2 ∣ a := by
    have : a % 2 = 0 := by omega
    omega
  obtain ⟨c, rfl⟩ := haeven
  have hcpos : 1 ≤ c := by omega
  -- `g = f^c ≥ 3`, and `(g - 1)(g + 1) = 2^b`
  set g : ℕ := f ^ c with hgdef
  have hgge : 3 ≤ g := by
    calc 3 ≤ f := hf3
      _ = f ^ 1 := (pow_one f).symm
      _ ≤ f ^ c := Nat.pow_le_pow_right (by omega) hcpos
  have hg2 : g ^ 2 = 2 ^ b + 1 := by
    rw [hgdef, ← pow_mul, mul_comm c 2]; exact h
  have hfactor : (g - 1) * (g + 1) = 2 ^ b := by
    have hge1 : 1 ≤ g := by omega
    zify [hge1]
    have : (g : ℤ) ^ 2 = 2 ^ b + 1 := by exact_mod_cast hg2
    linear_combination this
  -- both factors are powers of `2`, differing by `2`
  have hgm1 : (g - 1) ∣ 2 ^ b := ⟨g + 1, hfactor.symm⟩
  have hgp1 : (g + 1) ∣ 2 ^ b := ⟨g - 1, by rw [mul_comm]; exact hfactor.symm⟩
  obtain ⟨u, -, hu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hgm1
  obtain ⟨v, -, hv⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hgp1
  -- `2^v = 2^u + 2` with `u ≥ 1`, forcing `u = 1`, i.e. `g = 3`
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with rfl | hupos
    · rw [pow_zero] at hu; omega
    · exact hupos
  have huv : u < v := by
    have : (2 : ℕ) ^ u < 2 ^ v := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hudvd : (2 : ℕ) ^ u ∣ 2 := by
    have h1 : (2 : ℕ) ^ u ∣ 2 ^ v := pow_dvd_pow 2 huv.le
    have hveq : (2 : ℕ) ^ v = 2 ^ u + 2 := by omega
    rw [hveq] at h1
    exact (Nat.dvd_add_right (dvd_refl _)).mp h1
  have hule : (2 : ℕ) ^ u = 2 := by
    have hle := Nat.le_of_dvd (by norm_num) hudvd
    have hge : 2 ≤ (2 : ℕ) ^ u := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) hu1
    omega
  have hg3 : g = 3 := by omega
  -- `f^a = f^(2c) = (f^c)^2 = g^2 = 9`
  rw [mul_comm 2 c, pow_mul, ← hgdef, hg3]
  norm_num

/-- **Finite-field automorphisms for step (6)** (p. 110): the ring
automorphism group of a finite field of prime or prime-square order has
exponent at most `2` — every `σ` satisfies `σ² = 1`.

By `ringAut_card_prime_pow_eq_pow`, `σ x = x ^ (q^i)`; when `|F| = q` the
identity `x ^ q = x` makes `σ = 1`, and when `|F| = q²` we get
`σ² x = x ^ (q^{2i}) = x ^ (|F|^i) = x`.

Consumed by step (6) (field case) and step (8): `Σ` acts on the field `F`
by automorphisms, so `Σ` of odd order embeds into a group of exponent `2`
and is therefore trivial (when `|F| ∈ {f, 9}`). -/
theorem ringAut_sq_eq_one_of_card_prime_or_prime_sq {F : Type*} [Field F]
    [Finite F] {q : ℕ} (hq : q.Prime)
    (hcard : Nat.card F = q ∨ Nat.card F = q ^ 2) (σ : RingAut F) :
    σ ^ 2 = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hcardfin : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  have happ2 : ∀ x : F, (σ ^ 2) x = σ (σ x) := fun x => by rw [sq]; rfl
  ext x
  rw [happ2]
  change σ (σ x) = x
  rcases hcard with h1 | h2
  · -- `|F| = q`: `σ` is the identity
    obtain ⟨i, hi⟩ :=
      ringAut_card_prime_pow_eq_pow (q := q) (p := 1) (by rwa [pow_one]) σ
    have hfix : ∀ y : F, σ y = y := by
      intro y
      rw [hi y, ← h1, ← hcardfin]
      exact FiniteField.pow_card_pow i y
    rw [hfix, hfix]
  · -- `|F| = q²`: `σ² = 1`
    obtain ⟨i, hi⟩ := ringAut_card_prime_pow_eq_pow (q := q) (p := 2) h2 σ
    rw [hi (σ x), hi x, ← pow_mul]
    have hqq : q ^ i * q ^ i = (q ^ 2) ^ i := by rw [← pow_add, ← pow_mul]; congr 1; omega
    rw [hqq, ← h2, ← hcardfin]
    exact FiniteField.pow_card_pow i x

/-- **A commutative near-field is a field** (Peterfalvi, Appendix C,
Proposition 2, first alternative): a `NearField` with commutative
multiplication is a `Field`.

A near-field already carries `AddCommGroup` and `GroupWithZero`; only the
left distributive law (`NearField.mul_add_of_mul_comm`) and `mul_comm` are
missing.  Reusing the existing operations avoids `npow`/`nsmul` diamonds, so
the resulting field's `+`, `*`, `⁻¹` agree with the near-field's — hence a
near-field automorphism (`F ≃+ F` that is multiplicative) is a ring
automorphism of this field.

See note [reducible non-instances]: this is a `def`, invoked with `letI`
where a field structure on the commutative near-field is needed. -/
@[reducible] def NearFields.fieldOfComm {F : Type*} [inst : NearFields.NearField F]
    (hcomm : ∀ x y : F, x * y = y * x) : Field F :=
  { inst with
    mul_comm := hcomm
    left_distrib := fun a b c => NearFields.NearField.mul_add_of_mul_comm hcomm a b c
    right_distrib := NearFields.NearField.right_distrib
    nnqsmul := _
    nnqsmul_def := fun _ _ => rfl
    qsmul := _
    qsmul_def := fun _ _ => rfl }

/-- **The abstract core of step (6), field case** (p. 110): if the unit group
of a finite field `F` of characteristic `f` has order `2^b`, so that
`|F| = 2^b + 1`, then `|F| ∈ {f, 9}`; and any odd-order group `D` acting
faithfully by ring automorphisms is trivial.

By `FiniteField.card`, `|F| = f^a`; the arithmetic lemma
(`eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one`) gives `a = 1` (`|F| = f`)
or `f^a = 9`.  Then `|F|` is prime or prime-square, so `RingAut F` has
exponent `≤ 2` (`ringAut_sq_eq_one_of_card_prime_or_prime_sq`); an odd-order
subgroup of an exponent-`2` group is trivial. -/
theorem card_eq_and_aut_trivial_of_field_units_two_pow {F : Type*} [Field F]
    [Finite F] {f b : ℕ} (hf : f.Prime) [CharP F f] (hb : 1 ≤ b)
    (hFcard : Nat.card F = 2 ^ b + 1) {D : Type*} [Group D] [Finite D]
    (hDodd : Odd (Nat.card D)) (φ : D →* RingAut F)
    (hφinj : Function.Injective φ) :
    (Nat.card F = f ∨ Nat.card F = 9) ∧ Nat.card D = 1 := by
  haveI : Fact f.Prime := ⟨hf⟩
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨a, -, hcard_fa⟩ := FiniteField.card (K := F) f
  have hNcard : Nat.card F = f ^ (a : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcard_fa
  have heq : f ^ (a : ℕ) = 2 ^ b + 1 := by rw [← hNcard]; exact hFcard
  -- `f` is odd (else `2^a` even would equal the odd `2^b + 1`)
  have hfodd : Odd f := by
    rcases hf.eq_two_or_odd' with rfl | hodd
    · exfalso
      have hae : Even (2 ^ (a : ℕ)) :=
        even_iff_two_dvd.mpr (dvd_pow_self 2 a.pos.ne')
      rw [heq, Nat.even_add_one] at hae
      exact hae (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : b ≠ 0)))
    · exact hodd
  have hdich :=
    eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one hfodd hb heq
  have hFcard2 : Nat.card F = f ∨ Nat.card F = 9 := by
    rcases hdich with ha1 | hf9
    · left; rw [hNcard, ha1, pow_one]
    · right; rw [hNcard]; exact hf9
  refine ⟨hFcard2, ?_⟩
  -- every ring automorphism squares to the identity
  have hsq : ∀ σ : RingAut F, σ ^ 2 = 1 := by
    rcases hFcard2 with hf' | h9
    · exact fun σ => ringAut_sq_eq_one_of_card_prime_or_prime_sq hf (Or.inl hf') σ
    · exact fun σ => ringAut_sq_eq_one_of_card_prime_or_prime_sq (q := 3) (by norm_num)
        (Or.inr (by rw [h9]; norm_num)) σ
  -- an odd-order group faithfully in an exponent-`2` group is trivial
  have hDtriv : ∀ d : D, d = 1 := by
    intro d
    have hd2 : d ^ 2 = 1 := by
      apply hφinj
      rw [map_pow, map_one, hsq]
    have hord2 : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one hd2
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have hdvd : (2 : ℕ) ∣ Nat.card D := h2 ▸ orderOf_dvd_natCard d
      exact (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr hdvd)
  haveI : Subsingleton D := ⟨fun x y => by rw [hDtriv x, hDtriv y]⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G] (hyp : Hypothesis G Ω)

/-- **Step (6) plumbing**: if `Q₁ = 1` then `Q` is a `2`-group.  `Q₁` is the
odd normal `2`-complement of the nilpotent `Q`, so `Q₁ = 1` leaves `Q` equal to
its Sylow `2`-subgroup. -/
theorem card_Q_eq_two_pow_of_Q1_eq_bot (h : hyp.Q1 = ⊥) :
    ∃ n : ℕ, Nat.card ↥hyp.Q = 2 ^ n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥hyp.Q) := inferInstance
  have hcompl := hyp.sylowTwo_isComplement'_Q1Subgroup S
  have hQ1bot : hyp.Q1Subgroup = ⊥ := by
    have hc := hyp.card_Q1
    rw [h, Subgroup.card_bot] at hc
    exact Subgroup.eq_bot_of_card_eq _ hc.symm
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  refine ⟨n, ?_⟩
  have hmul := hcompl.card_mul
  rw [hQ1bot, Subgroup.card_bot, mul_one] at hmul
  rw [← hmul, hn]

end Hypothesis

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **The automorphism action `Σ = D → RingAut F`** (p. 110, field case): when
the near-field `F` of the model is commutative — hence a field via
`NearFields.fieldOfComm` — the model's `dAut` action of `D` by near-field
automorphisms is a group homomorphism into `RingAut F`.

`dAut g` is additive (`F ≃+ F`) and multiplicative (`dAut_mul`), so it is a ring
automorphism; the homomorphism property `dAut (g h) = dAut g ∘ dAut h` comes
from composing conjugations (`dAut_conj`) inside `G` and cancelling the
injective embedding `emb`. -/
noncomputable def dAutHom {F : Type uG} [NearFields.NearField F]
    (hcomm : ∀ x y : F, x * y = y * x)
    (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      NearFields.AffineNearFieldModel fc.rankOneQuotient F) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    letI := NearFields.fieldOfComm hcomm
    ↥fc.rankOneQuotient.D →* RingAut F :=
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  letI := NearFields.fieldOfComm hcomm
  { toFun := fun g => { model.dAut g with map_mul' := model.dAut_mul g }
    map_one' := by
      ext x
      have hconj := model.dAut_conj 1 x
      rw [OneMemClass.coe_one, one_mul, inv_one, mul_one] at hconj
      have : x = model.dAut 1 x :=
        Multiplicative.ofAdd.injective (model.emb_injective hconj)
      exact this.symm
    map_mul' := fun g h => by
      ext x
      -- `dAut (g h) x = dAut g (dAut h x)` from composing conjugations
      have hgh := model.dAut_conj (g * h) x
      have hh := model.dAut_conj h x
      have hg := model.dAut_conj g (model.dAut h x)
      rw [MulMemClass.coe_mul] at hgh
      have hkey : model.emb (Multiplicative.ofAdd (model.dAut (g * h) x)) =
          model.emb (Multiplicative.ofAdd (model.dAut g (model.dAut h x))) := by
        rw [← hgh, ← hg, ← hh]
        group
      exact Multiplicative.ofAdd.injective (model.emb_injective hkey) }

/-- **Peterfalvi Part II, Ch. II, step (6), field case** (p. 110): assume
`Q₁ = 1`.  If the near-field `F` of the model is commutative — hence a field —
then `|F| ∈ {f, 9}` (where `f` is the characteristic) and `Σ = D = 1`.

`Q₁ = 1` makes `Q` a `2`-group, so `|F^*| = |C_Q(P)|` is a power of `2` and
`|F| = 2^b + 1`; `Q_even` (transported through `model.qEquiv`) gives `b ≥ 1`.
The field-case abstract core
(`card_eq_and_aut_trivial_of_field_units_two_pow`) then finishes, fed the
automorphism homomorphism `dAutHom : D → RingAut F`.

Sorry-free as a `∀`-model statement; a caller supplying the model through
`exists_affineNearFieldModel` inherits the step (2)(b) `sorry` (issue 9318). -/
theorem card_field_eq_and_D_eq_one_of_comm :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ∀ {F : Type uG} [NearFields.NearField F]
      (model : NearFields.AffineNearFieldModel fc.rankOneQuotient F),
      fc.toHypothesis.Q1 = ⊥ → (∀ x y : F, x * y = y * x) →
      (Nat.card F = model.char ∨ Nat.card F = 9) ∧
        Nat.card ↥fc.rankOneQuotient.D = 1 := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  intro F instF model hQ1 hcomm
  classical
  letI : Field F := NearFields.fieldOfComm hcomm
  haveI : Finite F := by
    have hinj : Function.Injective
        (fun x : F => model.emb (Multiplicative.ofAdd x)) :=
      fun a b hab => Multiplicative.ofAdd.injective (model.emb_injective hab)
    exact Finite.of_injective _ hinj
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `|F^*| = |C_Q(P)|` is a power of `2` (from `Q₁ = 1`)
  obtain ⟨e⟩ := fc.centralizer_inf_mulEquiv_units model
  obtain ⟨n, hQn⟩ := fc.toHypothesis.card_Q_eq_two_pow_of_Q1_eq_bot hQ1
  have hCQdvd : Nat.card ↥(fc.toHypothesis.Q ⊓
      Subgroup.centralizer (fc.P : Set G)) ∣ 2 ^ n :=
    hQn ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, -, hCQm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hCQdvd
  have hFxcard : Nat.card Fˣ = 2 ^ m := (Nat.card_congr e.toEquiv).symm.trans hCQm
  -- `|F| = 2^m + 1`
  have hFcard : Nat.card F = 2 ^ m + 1 := by
    have hu := Nat.card_units F
    rw [hFxcard] at hu
    have hpos : 1 ≤ Nat.card F := Nat.card_pos
    omega
  -- `b = m ≥ 1`: `|F^*|` is even (`Q_even` via `qEquiv`)
  have hm : 1 ≤ m := by
    have hFxeven : Even (Nat.card Fˣ) := by
      rw [← Nat.card_congr model.qEquiv.toEquiv]
      exact fc.rankOneQuotient.Q_even
    rw [hFxcard] at hFxeven
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp at hFxeven
    · exact hpos
  -- `CharP F (model.char)`
  haveI : CharP F model.char := by
    have hchar0 : (model.char : F) = 0 := by
      have h := model.char_spec 1
      rwa [nsmul_eq_mul, mul_one] at h
    have hrc : ringChar F = model.char := by
      have hdvd : ringChar F ∣ model.char := ringChar.dvd hchar0
      rcases (Nat.Prime.eq_one_or_self_of_dvd model.char_prime _ hdvd) with h1 | h
      · exfalso
        haveI : CharP F 1 := h1 ▸ ringChar.charP F
        have h10 : (1 : F) = 0 := by
          have hc := (CharP.cast_eq_zero_iff F 1 1).mpr (dvd_refl 1)
          rwa [Nat.cast_one] at hc
        exact one_ne_zero h10
      · exact h
    rw [← hrc]; exact ringChar.charP F
  -- `dAutHom` is injective
  have hφinj : Function.Injective (fc.dAutHom hcomm model) := by
    intro g h hgh
    apply model.dAut_injective
    ext x
    exact DFunLike.congr_fun hgh x
  -- feed the abstract core
  exact card_eq_and_aut_trivial_of_field_units_two_pow model.char_prime hm hFcard
    fc.rankOneQuotient.D_odd (fc.dAutHom hcomm model) hφinj

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
