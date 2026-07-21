/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyReductionThree
import OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit

/-!
# Peterfalvi Appendix IV: the `Q₁`-component of induced members (step (3), Part B prep)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, p. 147 (campaign issue 1054).  Step (3) Part B writes each member
of `𝒮(S₂)` as `Ind_Q^H(λθ)` and anchors its Lemma 1(a) adjoins at
`Ind_Q^H(1·θ) ∈ 𝒳₁`.  This leaf builds the `θ`-side of that decomposition for
the internal direct product `Q = S × Q₁` **without** tensor-product character
theory:

* `exists_restrict_eq_nsmul` — **isotypic restriction**: for `φ ∈ Irr(Q)`,
  `Res_{Q₁} φ = e·θ` for a single irreducible `θ` and `e ≥ 1`.  By Clifford's
  single-orbit theorem (`restrictionConstituentsSingleOrbit_of_isIrreducible`)
  the constituents form one `Q`-conjugation orbit, and the `Q`-conjugation
  action on `Irr(Q₁)` is trivial (`conjBy_eq_self_of_isComplement'`): `S`
  centralises `Q₁` elementwise and `Q₁`-conjugation is inner.
* `q1Proj` — the projection `Q →* Q₁` of the direct product: the second
  component of the complement equivalence, multiplicative by uniqueness of the
  factorisation (`equiv_eq_of_mul_eq`).  The inflation `θ~ = θ ∘ q1Proj` and
  its irreducibility (norm folding) are the next layer on top of this leaf.

The `IsCharacter` transport bricks (`isCharacter_compHom`,
`isCharacter_restrict`) are `hyp`-independent and upstream-appropriate.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-! ## `IsCharacter` transport (hyp-independent) -/

/-- **Composition with a homomorphism preserves genuine characters**: if `χ` is
the character of `ρ`, then `χ ∘ f` is the character of `ρ ∘ f`. -/
theorem isCharacter_compHom {K K' : Type*} [Group K] [Group K'] (f : K' →* K)
    {χ : ClassFunction K ℂ} (hχ : IsCharacter χ) :
    IsCharacter (ClassFunction.compHom f χ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hχ
  refine ⟨V, inferInstance, inferInstance, inferInstance, ρ.comp f, ?_⟩
  funext x
  exact congrFun hρ (f x)

/-- **Restriction preserves genuine characters** (restriction is composition
with the inclusion). -/
theorem isCharacter_restrict {K : Type*} [Group K] (N : Subgroup K)
    {χ : ClassFunction K ℂ} (hχ : IsCharacter χ) :
    IsCharacter (ClassFunction.restrict N χ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hχ
  refine ⟨V, inferInstance, inferInstance, inferInstance, ρ.comp N.subtype, ?_⟩
  funext y
  exact congrFun hρ (y : K)

/-! ## Factorisation bookkeeping for a complement pair -/

/-- **Uniqueness of the complement factorisation**: if `↑a·↑b = q` then the
complement equivalence sends `q` to `(a, b)` (the equivalence is inverse to
multiplication). -/
theorem equiv_eq_of_mul_eq {K : Type*} [Group K] {A B : Subgroup K}
    (hAB : Subgroup.IsComplement' A B) {q : K} {a : ↥(A : Set K)}
    {b : ↥(B : Set K)} (h : (a : K) * (b : K) = q) :
    hAB.equiv q = (a, b) := by
  have hq : q = hAB.equiv.symm (a, b) := by rw [← h]; rfl
  rw [hq, Equiv.apply_symm_apply]

/-- `K`-level second-component form of `equiv_eq_of_mul_eq`: if `a·b = q` with
`a ∈ A`, `b ∈ B`, then the `B`-component of `q` is `b`. -/
theorem equiv_snd_eq_of_mul_eq {K : Type*} [Group K] {A B : Subgroup K}
    (hAB : Subgroup.IsComplement' A B) {q a b : K} (haA : a ∈ A) (hbB : b ∈ B)
    (h : a * b = q) : ((hAB.equiv q).2 : K) = b := by
  have heq := equiv_eq_of_mul_eq hAB (a := ⟨a, SetLike.mem_coe.mpr haA⟩)
    (b := ⟨b, SetLike.mem_coe.mpr hbB⟩) h
  rw [heq]

namespace Hypothesis

variable (hyp : Hypothesis G)

/-- Elements of the (doubly relativised) `S`- and `Q₁`-parts commute
(`S_commutes_Q1`, transported to `↥(Q.subgroupOf H)`). -/
theorem commute_of_mem_subgroupOf {a b : ↥(hyp.Q.subgroupOf hyp.H)}
    (ha : a ∈ (hyp.S.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))
    (hb : b ∈ (hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) :
    a * b = b * a := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at ha hb
  have h := hyp.S_commutes_Q1 _ ha _ hb
  exact Subtype.ext (Subtype.ext h)

/-- **The projection `Q →* Q₁` of the internal direct product `Q = S·Q₁`**,
doubly relativised: the second component of the complement equivalence
(`isComplement'_S_Q1_subgroupOf`), multiplicative by uniqueness of the
factorisation and the elementwise commuting of the two factors. -/
noncomputable def q1Proj :
    ↥(hyp.Q.subgroupOf hyp.H) →*
      ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) where
  toFun q :=
    ⟨((hyp.isComplement'_S_Q1_subgroupOf.equiv q).2 : ↥(hyp.Q.subgroupOf hyp.H)),
      SetLike.mem_coe.mp (hyp.isComplement'_S_Q1_subgroupOf.equiv q).2.2⟩
  map_one' := by
    apply Subtype.ext
    show ((hyp.isComplement'_S_Q1_subgroupOf.equiv 1).2 : ↥(hyp.Q.subgroupOf hyp.H)) = 1
    exact equiv_snd_eq_of_mul_eq hyp.isComplement'_S_Q1_subgroupOf
      (Subgroup.one_mem _) (Subgroup.one_mem _) (mul_one 1)
  map_mul' q₁ q₂ := by
    set e := hyp.isComplement'_S_Q1_subgroupOf.equiv with he
    have h1 : ((e q₁).1 : ↥(hyp.Q.subgroupOf hyp.H)) * ((e q₁).2 : _) = q₁ :=
      hyp.isComplement'_S_Q1_subgroupOf.equiv_fst_mul_equiv_snd q₁
    have h2 : ((e q₂).1 : ↥(hyp.Q.subgroupOf hyp.H)) * ((e q₂).2 : _) = q₂ :=
      hyp.isComplement'_S_Q1_subgroupOf.equiv_fst_mul_equiv_snd q₂
    have hcomm : ((e q₁).2 : ↥(hyp.Q.subgroupOf hyp.H)) * ((e q₂).1 : _)
        = ((e q₂).1 : ↥(hyp.Q.subgroupOf hyp.H)) * ((e q₁).2 : _) :=
      (hyp.commute_of_mem_subgroupOf (SetLike.mem_coe.mp (e q₂).1.2)
        (SetLike.mem_coe.mp (e q₁).2.2)).symm
    have hmul : (((e q₁).1 : ↥(hyp.Q.subgroupOf hyp.H)) * ((e q₂).1 : _))
        * (((e q₁).2 : ↥(hyp.Q.subgroupOf hyp.H)) * ((e q₂).2 : _)) = q₁ * q₂ :=
      calc (((e q₁).1 : ↥(hyp.Q.subgroupOf hyp.H)) * ((e q₂).1 : _))
            * (((e q₁).2 : _) * ((e q₂).2 : _))
          = ((e q₁).1 : ↥(hyp.Q.subgroupOf hyp.H))
            * (((e q₂).1 : _) * ((e q₁).2 : _)) * ((e q₂).2 : _) := by group
        _ = ((e q₁).1 : ↥(hyp.Q.subgroupOf hyp.H))
            * (((e q₁).2 : _) * ((e q₂).1 : _)) * ((e q₂).2 : _) := by rw [hcomm]
        _ = (((e q₁).1 : ↥(hyp.Q.subgroupOf hyp.H)) * ((e q₁).2 : _))
            * (((e q₂).1 : _) * ((e q₂).2 : _)) := by group
        _ = q₁ * q₂ := by rw [h1, h2]
    apply Subtype.ext
    show ((e (q₁ * q₂)).2 : ↥(hyp.Q.subgroupOf hyp.H))
      = ((e q₁).2 : ↥(hyp.Q.subgroupOf hyp.H)) * ((e q₂).2 : _)
    exact equiv_snd_eq_of_mul_eq hyp.isComplement'_S_Q1_subgroupOf
      (Subgroup.mul_mem _ (SetLike.mem_coe.mp (e q₁).1.2)
        (SetLike.mem_coe.mp (e q₂).1.2))
      (Subgroup.mul_mem _ (SetLike.mem_coe.mp (e q₁).2.2)
        (SetLike.mem_coe.mp (e q₂).2.2)) hmul

/-- The projection fixes the `Q₁`-part: `q1Proj q = q` for
`q ∈ (Q₁-in-H)-in-(Q-in-H)` (coe form). -/
theorem q1Proj_apply_coe_of_mem {q : ↥(hyp.Q.subgroupOf hyp.H)}
    (hq : q ∈ (hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) :
    ((hyp.q1Proj q : ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf
        (hyp.Q.subgroupOf hyp.H))) : ↥(hyp.Q.subgroupOf hyp.H)) = q := by
  show ((hyp.isComplement'_S_Q1_subgroupOf.equiv q).2 : ↥(hyp.Q.subgroupOf hyp.H)) = q
  exact equiv_snd_eq_of_mul_eq hyp.isComplement'_S_Q1_subgroupOf
    (Subgroup.one_mem _) hq (one_mul q)

/-- The projection kills the `S`-part: `q1Proj q = 1` for
`q ∈ (S-in-H)-in-(Q-in-H)`. -/
theorem q1Proj_apply_of_mem_S {q : ↥(hyp.Q.subgroupOf hyp.H)}
    (hq : q ∈ (hyp.S.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) :
    hyp.q1Proj q = 1 := by
  apply Subtype.ext
  show ((hyp.isComplement'_S_Q1_subgroupOf.equiv q).2 : ↥(hyp.Q.subgroupOf hyp.H)) = 1
  exact equiv_snd_eq_of_mul_eq hyp.isComplement'_S_Q1_subgroupOf
    hq (Subgroup.one_mem _) (mul_one q)

/-! ## The trivial `Q`-conjugation action on `Irr(Q₁)` -/

/-- **`Q`-conjugation acts trivially on class functions of `Q₁`**: writing
`g = a·b` with `a` in the `S`-part and `b` in the `Q₁`-part, conjugation by
`a` is the identity on `Q₁` (elementwise commuting) and conjugation by `b` is
inner.  This collapses the Clifford orbit of a constituent to a point. -/
theorem conjBy_eq_self_of_isComplement'
    [hN : ((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal]
    (g : ↥(hyp.Q.subgroupOf hyp.H))
    (θ : ClassFunction ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf
      (hyp.Q.subgroupOf hyp.H)) ℂ) :
    ClassFunction.conjBy g θ = θ := by
  apply Subtype.ext
  funext h
  rw [ClassFunction.conjBy_apply]
  set e := hyp.isComplement'_S_Q1_subgroupOf.equiv with he
  have hfac : ((e g).1 : ↥(hyp.Q.subgroupOf hyp.H)) * ((e g).2 : _) = g :=
    hyp.isComplement'_S_Q1_subgroupOf.equiv_fst_mul_equiv_snd g
  set a : ↥(hyp.Q.subgroupOf hyp.H) := ((e g).1 : ↥(hyp.Q.subgroupOf hyp.H)) with ha
  set b : ↥(hyp.Q.subgroupOf hyp.H) := ((e g).2 : ↥(hyp.Q.subgroupOf hyp.H)) with hb
  have haS : a ∈ (hyp.S.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H) :=
    SetLike.mem_coe.mp (e g).1.2
  have hbQ1 : b ∈ (hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H) :=
    SetLike.mem_coe.mp (e g).2.2
  -- `g h g⁻¹ = b h b⁻¹` in the ambient group: the `a`-part commutes through
  have hbhb : b * (h : ↥(hyp.Q.subgroupOf hyp.H)) * b⁻¹
      ∈ (hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hbQ1 h.2) (Subgroup.inv_mem _ hbQ1)
  have hkey : g * (h : ↥(hyp.Q.subgroupOf hyp.H)) * g⁻¹
      = b * (h : ↥(hyp.Q.subgroupOf hyp.H)) * b⁻¹ := by
    rw [← hfac]
    have hcomm := hyp.commute_of_mem_subgroupOf haS hbhb
    calc (a * b) * (h : ↥(hyp.Q.subgroupOf hyp.H)) * (a * b)⁻¹
        = a * (b * (h : ↥(hyp.Q.subgroupOf hyp.H)) * b⁻¹) * a⁻¹ := by group
      _ = (b * (h : ↥(hyp.Q.subgroupOf hyp.H)) * b⁻¹) * a * a⁻¹ := by
          rw [hcomm]
      _ = b * (h : ↥(hyp.Q.subgroupOf hyp.H)) * b⁻¹ := by group
  have hsub : (⟨g * (h : ↥(hyp.Q.subgroupOf hyp.H)) * g⁻¹,
        hN.conj_mem _ h.property g⟩ :
        ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)))
      = ⟨b, hbQ1⟩ * h * (⟨b, hbQ1⟩)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hkey
  rw [hsub]
  exact θ.conj_eq h ⟨b, hbQ1⟩

/-! ## Isotypic restriction: `Res_{Q₁} φ = e·θ` -/

set_option linter.unusedFintypeInType false in
/-- **Isotypic restriction to the direct factor** (Peterfalvi p. 147, step (3)
Part B): the restriction of `φ ∈ Irr(Q)` to `Q₁` is `e·θ` for a single
irreducible `θ` and `e ≥ 1`.  The constituents of `Res_{Q₁} φ` form one
`Q`-conjugation orbit (Clifford, `restrictionConstituentsSingleOrbit_of_
isIrreducible`), and the orbit is a point (`conjBy_eq_self_of_isComplement'`),
so the `ℕ`-decomposition of the genuine character `Res_{Q₁} φ`
(`IsCharacter.exists_natFinsupp_eq_sum`) has a single term. -/
theorem exists_restrict_eq_nsmul [Finite G] [Fintype ↥(hyp.Q.subgroupOf hyp.H)]
    [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]
    {φ : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ} (hφ : IsIrreducibleCharacter φ) :
    ∃ (θ : ClassFunction ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf
        (hyp.Q.subgroupOf hyp.H)) ℂ) (e : ℕ),
      IsIrreducibleCharacter θ ∧ 0 < e ∧
        ClassFunction.restrict ((hyp.Q1.subgroupOf hyp.H).subgroupOf
          (hyp.Q.subgroupOf hyp.H)) φ = (e : ℂ) • θ := by
  classical
  haveI : ((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal :=
    hyp.subgroupOf_Q_normal_of_conj_mem fun q hq x hx => hyp.Q1_conj_mem_of_mem_Q hq hx
  letI : Fintype ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) :=
    Fintype.ofFinite _
  letI : Invertible ((Nat.card ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf
      (hyp.Q.subgroupOf hyp.H)) : ℕ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set B := (hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H) with hBdef
  -- decompose the genuine character `Res_B φ`
  obtain ⟨m, hmsupp, hmsum, hmcoeff⟩ :=
    (isCharacter_restrict B hφ.isCharacter).exists_natFinsupp_eq_sum
  -- the support is nonempty: `Res φ` has nonzero degree
  have hsupp_ne : m.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    obtain ⟨d0, hd0, hd0val⟩ := hφ.exists_apply_one_eq_pos_natCast
    have h1 : ClassFunction.restrict B φ (1 : ↥B) = φ (1 : ↥(hyp.Q.subgroupOf hyp.H)) := by
      rw [ClassFunction.restrict_apply, OneMemClass.coe_one]
    have h0 : ClassFunction.restrict B φ (1 : ↥B) = 0 := by
      rw [hmsum, hempty, Finset.sum_empty]
      rfl
    rw [h1] at h0
    rw [show φ (1 : ↥(hyp.Q.subgroupOf hyp.H))
        = (φ : ↥(hyp.Q.subgroupOf hyp.H) → ℂ) 1 from rfl, hd0val] at h0
    exact (Nat.cast_ne_zero.mpr hd0.ne') h0
  obtain ⟨θ, hθsupp⟩ := hsupp_ne
  have hθirr : IsIrreducibleCharacter θ := hmsupp (Finset.mem_coe.mpr hθsupp)
  -- every support member equals `θ` (single orbit + trivial conjugation)
  have hLies : ∀ a, (ha : a ∈ m.support) →
      IrreducibleCharacter.LiesOver B (⟨φ, hφ⟩ : IrreducibleCharacter _)
        (⟨a, hmsupp (Finset.mem_coe.mpr ha)⟩ : IrreducibleCharacter ↥B) := by
    intro a ha
    have hane : (m a : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finsupp.mem_support_iff.mp ha)
    rw [hmcoeff a (hmsupp (Finset.mem_coe.mpr ha))] at hane
    intro h0
    rw [ClassFunction.restrictionMultiplicity_def] at h0
    exact hane h0
  have hsingle : ∀ a ∈ m.support, a = θ := by
    intro a ha
    obtain ⟨g, hg⟩ := restrictionConstituentsSingleOrbit_of_isIrreducible
      (H := B) (⟨φ, hφ⟩ : IrreducibleCharacter _)
      (⟨a, hmsupp (Finset.mem_coe.mpr ha)⟩ : IrreducibleCharacter ↥B)
      (⟨θ, hθirr⟩ : IrreducibleCharacter ↥B) (hLies a ha) (hLies θ hθsupp)
    have hcoe := congrArg (fun ξ : IrreducibleCharacter ↥B => (ξ : ClassFunction ↥B ℂ)) hg
    rw [IrreducibleCharacter.coe_conjBy] at hcoe
    rw [hyp.conjBy_eq_self_of_isComplement' g] at hcoe
    exact hcoe
  have hsupp_eq : m.support = {θ} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hθsupp, hsingle⟩
  refine ⟨θ, m θ, hθirr, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hθsupp), ?_⟩
  rw [hmsum, hsupp_eq, Finset.sum_singleton]

/-! ## The inflation `θ~ = θ ∘ q1Proj` -/

/-- **The projection `q1Proj` is surjective**: it fixes the `Q₁`-part pointwise
(`q1Proj_apply_coe_of_mem`), so every element of the target is its own image. -/
theorem q1Proj_surjective : Function.Surjective hyp.q1Proj := fun t =>
  ⟨(t : ↥(hyp.Q.subgroupOf hyp.H)),
    Subtype.ext (hyp.q1Proj_apply_coe_of_mem t.2)⟩

/-- **Restricting the inflation recovers `θ`**: `Res_{Q₁} (θ ∘ q1Proj) = θ`,
because `q1Proj` is the identity on the `Q₁`-part.  Together with
`IsIrreducibleCharacter.compHom_of_surjective` (via `q1Proj_surjective`) this
realises every `θ ∈ Irr(Q₁)` as the restriction of a member of `Irr(Q)` with
the `S`-part in its kernel. -/
theorem restrict_compHom_q1Proj
    (θ : ClassFunction ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf
      (hyp.Q.subgroupOf hyp.H)) ℂ) :
    ClassFunction.restrict ((hyp.Q1.subgroupOf hyp.H).subgroupOf
      (hyp.Q.subgroupOf hyp.H)) (ClassFunction.compHom hyp.q1Proj θ) = θ := by
  apply Subtype.ext
  funext t
  rw [ClassFunction.restrict_apply, ClassFunction.compHom_apply]
  exact congrArg θ (Subtype.ext (hyp.q1Proj_apply_coe_of_mem t.2))

/-- **The `S`-part lies in the kernel of the inflation**: for `s` in the
(doubly relativised) `S`-part, `(θ ∘ q1Proj) s = θ 1`. -/
theorem compHom_q1Proj_apply_of_mem_S
    (θ : ClassFunction ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf
      (hyp.Q.subgroupOf hyp.H)) ℂ)
    {s : ↥(hyp.Q.subgroupOf hyp.H)}
    (hs : s ∈ (hyp.S.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) :
    ClassFunction.compHom hyp.q1Proj θ s = θ 1 := by
  rw [ClassFunction.compHom_apply, hyp.q1Proj_apply_of_mem_S hs]

/-! ## The Part B anchor: `Ind_Q^H (θ ∘ q1Proj) ∈ 𝒳₁` -/

open scoped Classical in
/-- **The step (3) Part B anchor** (Peterfalvi p. 147, issue 1054): every
`ψ ∈ 𝒳(R, Z)` yields an anchor `χθ = Ind_Q^H (θ ∘ q1Proj) ∈ 𝒳₁ = 𝒳(S', Z)`
whose degree `d·θ(1)` divides `ψ(1) = d·(e·θ(1))`.  Here `θ` is the isotypic
`Q₁`-constituent of the inducing character `φ` of `ψ` (`exists_restrict_eq_nsmul`,
so `ψ(1) = d·φ(1) = d·e·θ(1)`); `Z ⊄ Ker θ` because otherwise `φ`, hence
`ψ = Ind φ`, would be constant on `Z` (`leKer_induce_of_forall`); the inflation
`θ~ = θ ∘ q1Proj` is irreducible (`compHom_of_surjective`) with the `S`-part in
its kernel, so `Ind θ~ ∈ 𝒮(S')`, and it is nonconstant on `Z` since a constant
induced character forces a constant inducing character
(`forall_eq_one_of_leKer`) while `θ~ = θ` on `Z ≤ Q₁`. -/
theorem exists_anchor_of_mem_XsetOf [Finite G]
    {R Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    (hZH : ∀ ⦃h : G⦄, h ∈ hyp.H → ∀ ⦃x : G⦄, x ∈ Z → h * x * h⁻¹ ∈ Z)
    {ψ : ClassFunction ↥hyp.H ℂ} (hψ : ψ ∈ hyp.XsetOf R Z) :
    ∃ (χθ : ClassFunction ↥hyp.H ℂ) (tθ e : ℕ),
      χθ ∈ hyp.XsetOf hyp.Sder Z ∧ 0 < tθ ∧ 0 < e ∧
      χθ (1 : ↥hyp.H) = (hyp.d : ℂ) * (tθ : ℂ) ∧
      ψ (1 : ↥hyp.H) = (hyp.d : ℂ) * ((e * tθ : ℕ) : ℂ) := by
  classical
  letI : Fintype ↥hyp.H := Fintype.ofFinite _
  letI : Fintype ↥(hyp.Q.subgroupOf hyp.H) := Fintype.ofFinite _
  letI : Invertible ((Nat.card G : ℕ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible ((Nat.card ↥hyp.H : ℕ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible ((Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℕ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨hψS, hψZ⟩ := hψ
  have hψSset : ψ ∈ hyp.Sset := hψS.1
  have hψ' := hψSset
  rw [Sset_eq_induced_of_Q hyp] at hψ'
  obtain ⟨φ, ⟨hφirr, -⟩, hψeq⟩ := hψ'
  obtain ⟨θ, e, hθirr, hepos, hres⟩ := hyp.exists_restrict_eq_nsmul hφirr
  -- evaluation of the isotypic identity on elements and at `1`
  have hφval : ∀ (z : ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))),
      φ (z : ↥(hyp.Q.subgroupOf hyp.H)) = (e : ℂ) * θ z := by
    intro z
    have h := congrArg (fun (f : ClassFunction
      ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)) ℂ) =>
      (f : _ → ℂ) z) hres
    simpa using h
  have hφ1 : φ (1 : ↥(hyp.Q.subgroupOf hyp.H)) = (e : ℂ) * θ 1 := by
    have h := hφval 1
    rwa [OneMemClass.coe_one] at h
  -- `Z ⊄ Ker θ`
  have hθZ : ¬ ∀ (z : ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))),
      (((z : ↥(hyp.Q.subgroupOf hyp.H)) : ↥hyp.H) : G) ∈ Z → θ z = θ 1 := by
    intro hconstθ
    apply hψZ
    rw [← hψeq]
    refine hyp.leKer_induce_of_forall (hZQ1.trans hyp.Q1_le_Q) hZH ?_
    intro y hy
    have hyB : y ∈ (hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H) :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (hZQ1 hy))
    rw [hφval ⟨y, hyB⟩, hconstθ ⟨y, hyB⟩ hy, ← hφ1]
  push Not at hθZ
  obtain ⟨z₀, hz₀Z, hz₀ne⟩ := hθZ
  -- the inflation `θ~` and its evaluation facts
  set θt : ClassFunction ↥(hyp.Q.subgroupOf hyp.H) ℂ :=
    ClassFunction.compHom hyp.q1Proj θ with hθt
  have hθtirr : IsIrreducibleCharacter θt :=
    IsIrreducibleCharacter.compHom_of_surjective hyp.q1Proj_surjective hθirr
  have hθtval : ∀ (z : ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))),
      θt (z : ↥(hyp.Q.subgroupOf hyp.H)) = θ z := by
    intro z
    rw [hθt, ClassFunction.compHom_apply]
    exact congrArg θ (Subtype.ext (hyp.q1Proj_apply_coe_of_mem z.2))
  have hθt1 : θt (1 : ↥(hyp.Q.subgroupOf hyp.H)) = θ 1 := by
    rw [hθt, ClassFunction.compHom_apply, map_one]
  -- `χθ = Ind θ~ ∈ 𝒮` (nonconstant on `Q₁` via the `Z`-witness `z₀`)
  have hχθS : ClassFunction.induce (hyp.Q.subgroupOf hyp.H) θt ∈ hyp.Sset := by
    rw [Sset_eq_induced_of_Q hyp]
    refine ⟨θt, ⟨hθtirr, ?_⟩, rfl⟩
    intro hallconst
    apply hz₀ne
    have h1 := hallconst (z₀ : ↥(hyp.Q.subgroupOf hyp.H)) (hZQ1 hz₀Z)
    rwa [hθtval z₀, hθt1] at h1
  -- `S' ⊆ Ker χθ`
  have hχθSder : hyp.LeKer (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) θt) hyp.Sder := by
    refine hyp.leKer_induce_of_forall hyp.Sder_le_Q
      (fun h hh x hx => hyp.Sder_conj_mem_of_mem_H hh hx) ?_
    intro y hy
    have hymem : y ∈ (hyp.S.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H) :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (hyp.Sder_le_S hy))
    have h1 : θt y = θ 1 := by
      rw [hθt]; exact hyp.compHom_q1Proj_apply_of_mem_S θ hymem
    rw [h1, hθt1]
  -- `Z ⊄ Ker χθ`
  have hχθirr : IsIrreducibleCharacter (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) θt) :=
    hyp.isIrreducibleCharacter_of_mem_Sset hχθS
  have hχθZ : ¬ hyp.LeKer (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) θt) Z := by
    intro hLK
    have hconst := hyp.forall_eq_one_of_leKer Z (hZQ1.trans hyp.Q1_le_Q) hθtirr hχθirr hLK
    apply hz₀ne
    have hx₀mem : (z₀ : ↥(hyp.Q.subgroupOf hyp.H)) ∈
        (Z.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H) :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hz₀Z)
    have h1 : θt (z₀ : ↥(hyp.Q.subgroupOf hyp.H)) = θt 1 := hconst ⟨_, hx₀mem⟩
    rwa [hθtval z₀, hθt1] at h1
  -- degrees
  obtain ⟨tθ, htθpos, htθval⟩ := hθirr.exists_apply_one_eq_pos_natCast
  have htθval' : θ (1 : ↥((hyp.Q1.subgroupOf hyp.H).subgroupOf
      (hyp.Q.subgroupOf hyp.H))) = (tθ : ℂ) := htθval
  have hχθ1 : (ClassFunction.induce (hyp.Q.subgroupOf hyp.H) θt) (1 : ↥hyp.H)
      = (hyp.d : ℂ) * (tθ : ℂ) := by
    rw [ClassFunction.induce_apply_one, hyp.index_Q_subgroupOf_eq_d, hθt1, htθval']
  have hψ1 : ψ (1 : ↥hyp.H) = (hyp.d : ℂ) * ((e * tθ : ℕ) : ℂ) := by
    rw [← hψeq, ClassFunction.induce_apply_one, hyp.index_Q_subgroupOf_eq_d, hφ1, htθval']
    push_cast
    ring
  exact ⟨ClassFunction.induce (hyp.Q.subgroupOf hyp.H) θt, tθ, e,
    ⟨⟨hχθS, hχθSder⟩, hχθZ⟩, htθpos, hepos, hχθ1, hψ1⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
