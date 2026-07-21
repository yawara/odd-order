/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.SquareCosetFiber
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.KSubgroupOrbit
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.SplitUniqueness

/-!
# Peterfalvi Part II, Ch. I §3, Lemma 5: the conjugate summand split

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, Lemma 5, p. 107.

Let `ω` be an odd-order automorphism of `Q` which fixes `Q₀` pointwise,
commutes with the `K`-action, and whose nontrivial powers have all their
fixed points inside `Q₀` (in the source, conjugation by `1 ≠ w ∈ W`).  If
`ω` stabilized a summand `X̄` of `Q ⧸ Q₀`, it would stabilize the unique
`Q₀`-coset with square `s` inside it (`existsUnique_cosetSquare_eq`), and
coprime fixed-point lifting would produce an `ω`-fixed representative outside
`Q₀` — contradicting the centralizer computation `C_Q(w) = Q₀`.  Hence
`X̄^ω ≠ X̄`, and the pair `(X̄, X̄^ω)` together with the equivariant
isomorphism `ω` itself forms an `IsomorphicOrderQModuleSplit`, the input of
the type-B recognition of Appendix III, Theorem (e).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

universe uK uP

variable {P : Type uP} [Group P]

/-! ## The induced automorphism of the central quotient -/

section InducedAut

variable {Z : Subgroup P} [Z.Normal]

omit [Z.Normal] in
/-- An automorphism fixing `Z` pointwise maps `Z` onto itself. -/
theorem map_eq_of_forall_fixed {ω : MulAut P} (hωZ : ∀ z ∈ Z, ω z = z) :
    Z.map ω.toMonoidHom = Z := by
  apply le_antisymm
  · rintro x ⟨z, hz, rfl⟩
    change ω z ∈ Z
    rw [hωZ z hz]
    exact hz
  · intro z hz
    exact ⟨z, hz, hωZ z hz⟩

/-- The automorphism induced on `P ⧸ Z` by an automorphism of `P` fixing `Z`
pointwise. -/
def quotientCongr (ω : MulAut P) (hωZ : ∀ z ∈ Z, ω z = z) :
    MulAut (P ⧸ Z) :=
  QuotientGroup.congr Z Z ω (map_eq_of_forall_fixed hωZ)

@[simp]
theorem quotientCongr_mk (ω : MulAut P) (hωZ : ∀ z ∈ Z, ω z = z) (x : P) :
    quotientCongr ω hωZ (QuotientGroup.mk x) = QuotientGroup.mk (ω x) := rfl

/-- The induced automorphism of a product is the composite of the induced
automorphisms. -/
theorem quotientCongr_mul_apply (ω₁ ω₂ : MulAut P)
    (h₁ : ∀ z ∈ Z, ω₁ z = z) (h₂ : ∀ z ∈ Z, ω₂ z = z)
    (h₁₂ : ∀ z ∈ Z, (ω₁ * ω₂) z = z) (q : P ⧸ Z) :
    quotientCongr (ω₁ * ω₂) h₁₂ q =
      quotientCongr ω₁ h₁ (quotientCongr ω₂ h₂ q) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [quotientCongr_mk]
  rfl

/-- The identity automorphism induces the identity on the quotient. -/
theorem quotientCongr_one_apply (h : ∀ z ∈ Z, (1 : MulAut P) z = z)
    (q : P ⧸ Z) :
    quotientCongr 1 h q = q := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [quotientCongr_mk]
  rfl

/-- An automorphism commuting with an action of `K` on `P` induces an
automorphism of `P ⧸ Z` commuting with the induced action. -/
theorem quotientCongr_comm_quotientMulAutHom
    {K : Type uK} [Group K]
    {rho : K →* MulAut P} (hZinv : OddOrder.Isaacs.Ch03.IsAInvariant rho Z)
    (ω : MulAut P) (hωZ : ∀ z ∈ Z, ω z = z)
    (k : K) (hcomm : Commute (rho k) ω) (q : P ⧸ Z) :
    quotientCongr ω hωZ (quotientMulAutHom hZinv k q) =
      quotientMulAutHom hZinv k (quotientCongr ω hωZ q) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [show quotientMulAutHom hZinv k (QuotientGroup.mk x) =
      QuotientGroup.mk (rho k x) from rfl, quotientCongr_mk,
    quotientCongr_mk,
    show quotientMulAutHom hZinv k (QuotientGroup.mk (ω x)) =
      QuotientGroup.mk (rho k (ω x)) from rfl]
  have happ : rho k (ω x) = ω (rho k x) := by
    calc rho k (ω x) = (rho k * ω) x := rfl
      _ = (ω * rho k) x := by rw [hcomm.eq]
      _ = ω (rho k x) := rfl
  rw [happ]

end InducedAut

/-! ## The conjugate summand and the isomorphic split -/

section ConjugateSplit

variable [Finite P]
variable {K : Type uK} [Group K]
variable {Z : Subgroup P} [Z.Normal]
variable {rho : K →* MulAut P} {hZinv : IsAInvariant rho Z}

/-- **The moved-summand contradiction** (Peterfalvi Part II, Ch. I §3,
Lemma 5, p. 107).  A nontrivial odd-order automorphism `ω` of `P` fixing `Z`
pointwise, whose nontrivial powers have all their fixed points inside `Z`,
cannot stabilize an invariant summand of order `|Z|`: it would stabilize the
unique coset with square `s`, and coprime fixed-point lifting would produce a
fixed representative outside `Z`. -/
theorem map_quotientCongr_ne_of_fixedPoints_le
    (hZle : Z ≤ Subgroup.center P) (hZsq : ∀ z ∈ Z, z ^ 2 = 1)
    (hAgemo : ∀ x : P, x ^ 2 ∈ Z) (hinvZ : ∀ x : P, x ^ 2 = 1 → x ∈ Z)
    {Xbar : Subgroup (P ⧸ Z)}
    (hXinv : IsAInvariant (quotientMulAutHom hZinv) Xbar)
    (hXcard : Nat.card ↥Xbar = Nat.card ↥Z)
    (htransZ : ∀ s₁ s₂ : P, s₁ ∈ Z → s₁ ≠ 1 → s₂ ∈ Z → s₂ ≠ 1 →
      ∃ k : K, rho k s₁ = s₂)
    (hZbot : Z ≠ ⊥)
    (ω : MulAut P) (hω1 : ω ≠ 1) (hωodd : Odd (orderOf ω))
    (hωZ : ∀ z ∈ Z, ω z = z)
    (hωfix : ∀ m : ℕ, ω ^ m ≠ 1 → ∀ x : P, (ω ^ m) x = x → x ∈ Z) :
    Xbar.map (quotientCongr ω hωZ).toMonoidHom ≠ Xbar := by
  intro hstab
  classical
  -- a nonidentity central involution `s`
  obtain ⟨s, hsZ, hsbot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hZbot)
  have hs1 : s ≠ 1 := by
    intro h1
    exact hsbot (by rw [h1]; exact Subgroup.one_mem ⊥)
  -- the unique coset of the summand with square `s`
  obtain ⟨q₀, hq₀X, hq₀sq, hq₀uniq⟩ :=
    existsUnique_cosetSquare_eq hZle hZsq hZinv hAgemo hinvZ hXinv hXcard
      htransZ hsZ hs1
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective q₀
  have hx₀sq : x₀ ^ 2 = s := hq₀sq
  have hx₀Z : x₀ ∉ Z := by
    intro hmem
    exact hs1 (hx₀sq ▸ hZsq x₀ hmem)
  -- powers of `ω` fix `Z` pointwise and stabilize the summand
  have hpowZ : ∀ m : ℕ, ∀ z ∈ Z, (ω ^ m) z = z := by
    intro m
    induction m with
    | zero => intro z _; rfl
    | succ i ih =>
        intro z hz
        rw [pow_succ, MulAut.mul_apply, hωZ z hz, ih z hz]
  have hmempow : ∀ m : ℕ, QuotientGroup.mk ((ω ^ m) x₀) ∈ Xbar := by
    intro m
    induction m with
    | zero =>
        rw [pow_zero]
        simpa using hq₀X
    | succ i ih =>
        have hstep : QuotientGroup.mk ((ω ^ (i + 1)) x₀) =
            quotientCongr ω hωZ (QuotientGroup.mk ((ω ^ i) x₀)) := by
          rw [quotientCongr_mk, pow_succ', MulAut.mul_apply]
        rw [hstep]
        have hmem : quotientCongr ω hωZ (QuotientGroup.mk ((ω ^ i) x₀)) ∈
            Xbar.map (quotientCongr ω hωZ).toMonoidHom :=
          ⟨QuotientGroup.mk ((ω ^ i) x₀), ih, rfl⟩
        rwa [hstab] at hmem
  -- the coset of `x₀` is invariant under every power of `ω`
  have hcoset : ∀ m : ℕ, ∃ z ∈ Z, (ω ^ m) x₀ = x₀ * z := by
    intro m
    have hsq : cosetSquare Z hZle hZsq (QuotientGroup.mk ((ω ^ m) x₀)) =
        s := by
      rw [cosetSquare_mk, ← map_pow, hx₀sq]
      exact hpowZ m s hsZ
    have heq := hq₀uniq _ (hmempow m) hsq
    rw [QuotientGroup.eq] at heq
    refine ⟨x₀⁻¹ * (ω ^ m) x₀, ?_, by group⟩
    have hinveq : (((ω ^ m) x₀)⁻¹ * x₀)⁻¹ = x₀⁻¹ * (ω ^ m) x₀ := by group
    rw [← hinveq]
    exact Z.inv_mem heq
  -- coprime fixed-point lifting in the invariant coset
  let C : Subgroup (MulAut P) := Subgroup.zpowers ω
  let psi : ↥C →* MulAut P := C.subtype
  have hZpsi : IsAInvariant psi Z := by
    intro c
    have hZfix : ∀ z ∈ Z, (c : MulAut P) z = z := by
      intro z hz
      obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers).mpr c.2
      rw [← hm]
      exact hpowZ m z hz
    exact map_eq_of_forall_fixed hZfix
  have hZ2 : IsPGroup 2 ↥Z := by
    intro z
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one]
    simpa using hZsq (z : P) z.2
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  have hCodd : Odd (Nat.card ↥C) := by
    have : Nat.card ↥C = orderOf ω := Nat.card_zpowers ω
    rwa [this]
  have hcop : Nat.Coprime (Nat.card ↥C) (Nat.card ↥Z) := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr hCodd).pow_right n
  have hcosetC : ∀ c : ↥C, ∃ z ∈ Z, psi c x₀ = x₀ * z := by
    intro c
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers).mpr c.2
    obtain ⟨z, hzZ, hz⟩ := hcoset m
    refine ⟨z, hzZ, ?_⟩
    change (c : MulAut P) x₀ = x₀ * z
    rw [← hm]
    exact hz
  haveI : IsSolvable ↥C :=
    isSolvable_of_comm fun c d => mul_comm' c d
  obtain ⟨x, hxfix, z, hzZ, hx⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
      (φ := psi) hcop (Or.inl (inferInstance : IsSolvable ↥C)) hZpsi hcosetC
  have hωx : ω x = x := by
    have := hxfix ⟨ω, Subgroup.mem_zpowers ω⟩
    simpa [psi] using this
  have hxZ : x ∈ Z := by
    refine hωfix 1 (by simpa using hω1) x ?_
    simpa using hωx
  apply hx₀Z
  have hx₀eq : x₀ = x * z⁻¹ := by
    rw [hx]
    group
  rw [hx₀eq]
  exact Z.mul_mem hxZ (Z.inv_mem hzZ)

/-- **The conjugate summand split** (Peterfalvi Part II, Ch. I §3, Lemma 5,
p. 107).  Under the hypotheses above, together with commutation of `ω` with
the `K`-action, the pair `(X̄, X̄^ω)` is an invariant two-summand split of
`P ⧸ Z` whose summands are equivariantly isomorphic via `ω`. -/
theorem nonempty_isomorphicOrderQModuleSplit_of_commuting_automorphism
    (hZle : Z ≤ Subgroup.center P) (hZsq : ∀ z ∈ Z, z ^ 2 = 1)
    (hAgemo : ∀ x : P, x ^ 2 ∈ Z) (hinvZ : ∀ x : P, x ^ 2 = 1 → x ∈ Z)
    (csplit : OrderQModuleSplit rho Z hZinv)
    (htransZ : ∀ s₁ s₂ : P, s₁ ∈ Z → s₁ ≠ 1 → s₂ ∈ Z → s₂ ≠ 1 →
      ∃ k : K, rho k s₁ = s₂)
    (hfree : ∀ k : K, k ≠ 1 → ∀ q : P ⧸ Z,
      quotientMulAutHom hZinv k q = q → q = 1)
    (hcardK : Nat.card K = Nat.card ↥Z - 1)
    (hZbot : Z ≠ ⊥)
    (ω : MulAut P) (hω1 : ω ≠ 1) (hωodd : Odd (orderOf ω))
    (hωZ : ∀ z ∈ Z, ω z = z)
    (hωcomm : ∀ k : K, Commute (rho k) ω)
    (hωfix : ∀ m : ℕ, ω ^ m ≠ 1 → ∀ x : P, (ω ^ m) x = x → x ∈ Z) :
    Nonempty (IsomorphicOrderQModuleSplit rho Z hZinv) := by
  classical
  set Xbar := csplit.left with hXdef
  set Ybar := Xbar.map (quotientCongr ω hωZ).toMonoidHom with hYdef
  -- quotient-level commutation of `ω` with the induced action
  have hcommQ : ∀ (k : K) (q : P ⧸ Z),
      quotientCongr ω hωZ (quotientMulAutHom hZinv k q) =
        quotientMulAutHom hZinv k (quotientCongr ω hωZ q) := fun k q =>
    quotientCongr_comm_quotientMulAutHom hZinv ω hωZ k (hωcomm k) q
  -- invariance of the conjugate summand
  have hYinv : IsAInvariant (quotientMulAutHom hZinv) Ybar := by
    intro k
    change Ybar.map (quotientMulAutHom hZinv k).toMonoidHom = Ybar
    have hcompeq : (quotientMulAutHom hZinv k).toMonoidHom.comp
        (quotientCongr ω hωZ).toMonoidHom =
        (quotientCongr ω hωZ).toMonoidHom.comp
          (quotientMulAutHom hZinv k).toMonoidHom :=
      MonoidHom.ext fun q => (hcommQ k q).symm
    calc Ybar.map (quotientMulAutHom hZinv k).toMonoidHom
        = Xbar.map ((quotientMulAutHom hZinv k).toMonoidHom.comp
            (quotientCongr ω hωZ).toMonoidHom) := by
          rw [hYdef, Subgroup.map_map]
      _ = Xbar.map ((quotientCongr ω hωZ).toMonoidHom.comp
            (quotientMulAutHom hZinv k).toMonoidHom) := by rw [hcompeq]
      _ = (Xbar.map (quotientMulAutHom hZinv k).toMonoidHom).map
            (quotientCongr ω hωZ).toMonoidHom := by rw [Subgroup.map_map]
      _ = Ybar := by
          rw [show Xbar.map (quotientMulAutHom hZinv k).toMonoidHom = Xbar
            from csplit.leftInvariant k]
  -- cardinality of the conjugate summand
  have hYcard : Nat.card ↥Ybar = Nat.card ↥Z := by
    rw [hYdef]
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective Xbar
      (quotientCongr ω hωZ).toMonoidHom
      (quotientCongr ω hωZ).injective).toEquiv]
    exact csplit.leftCard
  -- the two summands are distinct
  have hne : Xbar ≠ Ybar := by
    intro heq
    exact map_quotientCongr_ne_of_fixedPoints_le hZle hZsq hAgemo hinvZ
      csplit.leftInvariant csplit.leftCard htransZ hZbot ω hω1 hωodd hωZ
      hωfix heq.symm
  -- transitivity of `K` on the nonidentity elements of the summand
  have htransX : ∀ a b : ↥Xbar, a ≠ 1 → b ≠ 1 →
      ∃ k : K, csplit.leftInvariant.restrict k a = b :=
    restrict_transitive_of_fixedPointFree_card (quotientMulAutHom hZinv)
      hfree csplit.leftInvariant
      (by rw [csplit.leftCard]; exact hcardK)
  -- the ambient product formula
  haveI hLnormal : Xbar.Normal :=
    normal_of_mul_comm csplit.quotientEA.comm _
  have hmul : Nat.card ↥Xbar * Nat.card ↥Ybar = Nat.card (P ⧸ Z) := by
    calc Nat.card ↥Xbar * Nat.card ↥Ybar
        = Nat.card ((P ⧸ Z) ⧸ Xbar) * Nat.card ↥Xbar := by
          rw [card_quotient_of_isCompl csplit.complementary,
            csplit.rightCard, hYcard, csplit.leftCard, Nat.mul_comm]
      _ = Nat.card (P ⧸ Z) :=
          (Subgroup.card_eq_card_quotient_mul_card_subgroup Xbar).symm
  have hcompl : IsCompl Xbar Ybar :=
    isCompl_of_distinct_invariant_of_transitive_card
      (quotientMulAutHom hZinv) csplit.leftInvariant hYinv htransX hne
      (csplit.leftCard.trans hYcard.symm) hmul
  -- the equivariant isomorphism between the summands
  let eSummand : ↥Xbar ≃* ↥Ybar :=
    MulEquiv.subgroupMap (quotientCongr ω hωZ) Xbar
  have hequivariant : ∀ (k : K) (x : ↥Xbar),
      eSummand (csplit.leftInvariant.restrict k x) =
        hYinv.restrict k (eSummand x) := by
    intro k x
    apply Subtype.ext
    change quotientCongr ω hωZ
        ((csplit.leftInvariant.restrict k x : ↥Xbar) : P ⧸ Z) =
      ((hYinv.restrict k (eSummand x) : ↥Ybar) : P ⧸ Z)
    rw [IsAInvariant.restrict_apply_val, IsAInvariant.restrict_apply_val]
    exact hcommQ k (x : P ⧸ Z)
  exact ⟨{
    split := {
      quotientEA := csplit.quotientEA
      left := Xbar
      right := Ybar
      leftInvariant := csplit.leftInvariant
      rightInvariant := hYinv
      leftCard := csplit.leftCard
      rightCard := hYcard
      complementary := hcompl }
    summandEquiv := {
      toMulEquiv := eSummand
      equivariant := hequivariant } }⟩

end ConjugateSplit

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
