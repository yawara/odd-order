/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepSeven

/-!
# Peterfalvi Part II, Ch. II, step (8): the case `Q₁ ≠ 1`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (8), p. 110.

Assume `Q₁ ≠ 1`.  Let `ℓ = |Σ|`.  If `ℓ ≠ 1`, then `ℓ` is prime and `F` is a
field of order `3^ℓ`, `5^ℓ`, or `9^ℓ`.

The first step of the argument is that `F` is a *field*: by step (5) the model's
near-field is either commutative or `≅ F_{9,2}`, and the exceptional near-field
`F_{9,2}` occurs only with `Q₁ = 1`.  So `Q₁ ≠ 1` forces `F` commutative.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

/-- Package an additive automorphism of a field that is also multiplicative as a
ring automorphism (`σ_w` for step (8): the model's `dAut g` is `F ≃+ F` and
multiplicative by `dAut_mul`). -/
def ringEquivOfAddEquivMul {F : Type*} [Field F] (a : F ≃+ F)
    (hmul : ∀ x y : F, a (x * y) = a x * a y) : F ≃+* F :=
  { a with map_mul' := hmul }

theorem ringEquivOfAddEquivMul_apply {F : Type*} [Field F] (a : F ≃+ F)
    (hmul : ∀ x y : F, a (x * y) = a x * a y) (x : F) :
    ringEquivOfAddEquivMul a hmul x = a x := rfl

/-- **Fixed field = fixed units + `0`** (step (8), p. 110): the fixed set of a
ring automorphism `σ` of a finite field has one more element than the fixed
units — the extra element is `0`. -/
theorem card_fixedSet_eq_card_fixedUnits_add_one {F : Type*} [Field F] [Finite F]
    (σ : F ≃+* F) :
    Nat.card {x : F // σ x = x} =
      Nat.card {u : Fˣ // σ (u : F) = (u : F)} + 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  let e : {x : F // σ x = x} ≃ Option {u : Fˣ // σ (u : F) = (u : F)} :=
    { toFun := fun x => if hx : (x : F) = 0 then none
        else some ⟨Units.mk0 (x : F) hx, x.2⟩
      invFun := fun o => o.elim ⟨0, map_zero σ⟩ (fun u => ⟨(u : Fˣ), u.2⟩)
      left_inv := fun x => by
        by_cases hx : (x : F) = 0
        · simp only [dif_pos hx, Option.elim]; exact Subtype.ext hx.symm
        · simp only [dif_neg hx, Option.elim, Units.val_mk0]
      right_inv := fun o => by
        cases o with
        | none => simp only [Option.elim, dif_pos]
        | some u =>
          have hu : ((u : Fˣ) : F) ≠ 0 := (u : Fˣ).ne_zero
          simp only [Option.elim, dif_neg hu]
          exact congrArg some (Subtype.ext (Units.ext (by simp))) }
  haveI : Fintype {u : Fˣ // σ (u : F) = (u : F)} := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option,
    ← Nat.card_eq_fintype_card]

section ModelDAut

variable {G' Ω' : Type*} [Group G'] [MulAction G' Ω'] [Finite G']
  {hyp : NearFields.RankOneHypothesis G' Ω'} {F : Type*} [NearFields.NearField F]
  (model : NearFields.AffineNearFieldModel hyp F)

/-- **`dAut 1 = id`**: the model's automorphism action sends the identity of `D`
to the identity automorphism (the conjugation by `1` fixes `emb`). -/
theorem model_dAut_one (x : F) : model.dAut 1 x = x := by
  have hconj := model.dAut_conj 1 x
  rw [OneMemClass.coe_one, one_mul, inv_one, mul_one] at hconj
  exact (Multiplicative.ofAdd.injective (model.emb_injective hconj)).symm

/-- **`dAut` is a homomorphism**: `dAut (g h) = dAut g ∘ dAut h`, obtained by
composing the conjugations realizing `dAut`. -/
theorem model_dAut_hom (g h : ↥hyp.D) (x : F) :
    model.dAut (g * h) x = model.dAut g (model.dAut h x) := by
  have hgh := model.dAut_conj (g * h) x
  have hh := model.dAut_conj h x
  have hg := model.dAut_conj g (model.dAut h x)
  rw [MulMemClass.coe_mul] at hgh
  have hkey : model.emb (Multiplicative.ofAdd (model.dAut (g * h) x)) =
      model.emb (Multiplicative.ofAdd (model.dAut g (model.dAut h x))) := by
    rw [← hgh, ← hg, ← hh]; group
  exact Multiplicative.ofAdd.injective (model.emb_injective hkey)

/-- **`dAut g` and `dAut g⁻¹` are mutually inverse**. -/
theorem model_dAut_inv_cancel (g : ↥hyp.D) (x : F) :
    model.dAut g (model.dAut g⁻¹ x) = x := by
  rw [← model_dAut_hom model g g⁻¹ x, mul_inv_cancel, model_dAut_one]

/-- **`qEquiv` intertwines `D`-conjugation on `Q` with `dAut` on `F^*`**
(step (8), the equivariance): for `g ∈ D` and `q ∈ Q`, the `Q`-conjugate
`g q g⁻¹` maps under `qEquiv` to `dAut g` applied to `qEquiv q`.

Conjugating `emb(1)` by `g q g⁻¹` and unwinding through `dAut_conj` (for `g`,
`g⁻¹`) and `qEquiv_conj` (for `q`) computes to `emb(1 · dAut g ↑(qEquiv q))`;
comparing with `qEquiv_conj` for the conjugate and cancelling `emb`, `ofAdd`
gives the identity. -/
theorem model_qEquiv_conj (g : ↥hyp.D) (q : ↥hyp.Q)
    (hc : (g : G') * (q : G') * (g : G')⁻¹ ∈ hyp.Q) :
    ((model.qEquiv ⟨(g : G') * (q : G') * (g : G')⁻¹, hc⟩ : Fˣ) : F) =
      model.dAut g ((model.qEquiv q : Fˣ) : F) := by
  set u : F := ((model.qEquiv q : Fˣ) : F) with hu
  set c : G' := (g : G') * (q : G') * (g : G')⁻¹ with hc_def
  have hy : ((g : G'))⁻¹ * model.emb (Multiplicative.ofAdd (1 : F)) * (g : G') =
      model.emb (Multiplicative.ofAdd (model.dAut g⁻¹ (1 : F))) := by
    have h := model.dAut_conj g⁻¹ (1 : F)
    rwa [Subgroup.coe_inv, inv_inv] at h
  have hq := model.qEquiv_conj q (model.dAut g⁻¹ (1 : F))
  have hgg := model.dAut_conj g (model.dAut g⁻¹ (1 : F) * u)
  have hval : model.dAut g (model.dAut g⁻¹ (1 : F) * u) = 1 * model.dAut g u := by
    rw [model.dAut_mul g, model_dAut_inv_cancel model g (1 : F)]
  have hchain : c * model.emb (Multiplicative.ofAdd (1 : F)) * c⁻¹ =
      model.emb (Multiplicative.ofAdd (1 * model.dAut g u)) := by
    calc c * model.emb (Multiplicative.ofAdd (1 : F)) * c⁻¹
        = (g : G') * ((q : G') * (((g : G'))⁻¹ *
            model.emb (Multiplicative.ofAdd (1 : F)) * (g : G')) *
            (q : G')⁻¹) * (g : G')⁻¹ := by rw [hc_def]; group
      _ = (g : G') * ((q : G') *
            model.emb (Multiplicative.ofAdd (model.dAut g⁻¹ (1 : F))) *
            (q : G')⁻¹) * (g : G')⁻¹ := by rw [hy]
      _ = (g : G') * model.emb
            (Multiplicative.ofAdd (model.dAut g⁻¹ (1 : F) * u)) * (g : G')⁻¹ := by
            rw [hq]
      _ = model.emb (Multiplicative.ofAdd
            (model.dAut g (model.dAut g⁻¹ (1 : F) * u))) := by rw [hgg]
      _ = model.emb (Multiplicative.ofAdd (1 * model.dAut g u)) := by rw [hval]
  have hr := model.qEquiv_conj ⟨c, hc⟩ (1 : F)
  rw [hchain] at hr
  have hfin := Multiplicative.ofAdd.injective (model.emb_injective hr.symm)
  rwa [one_mul, one_mul] at hfin

/-- **`qEquiv` matches fixed units with conjugation-fixed `Q`** (step (8)): for
`g ∈ D` (inside `H`), `qEquiv` restricts to a bijection between the elements of
`Q` fixed by `g`-conjugation and the units of `F` fixed by `dAut g`.  Hence the
two counts agree. -/
theorem card_fixedUnits_eq_card_fixedConj (g : ↥hyp.D) (hgH : (g : G') ∈ hyp.H) :
    Nat.card {u : Fˣ // model.dAut g (u : F) = (u : F)} =
      Nat.card {q : ↥hyp.Q // (g : G') * (q : G') * (g : G')⁻¹ = (q : G')} := by
  classical
  have hnorm : ∀ q : ↥hyp.Q, (g : G') * (q : G') * (g : G')⁻¹ ∈ hyp.Q :=
    fun q => hyp.Q_normal_in_H (g : G') hgH (q : G') q.2
  refine (Nat.card_congr ?_).symm
  refine
    { toFun := fun q => ⟨model.qEquiv q.1, ?_⟩
      invFun := fun u => ⟨model.qEquiv.symm u.1, ?_⟩
      left_inv := fun q => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp) }
  · -- fixed conjugation ⟹ fixed unit
    have hc := hnorm q.1
    have hkey := model_qEquiv_conj model g q.1 hc
    have hq : (⟨(g : G') * (q.1 : G') * (g : G')⁻¹, hc⟩ : ↥hyp.Q) = q.1 :=
      Subtype.ext q.2
    rw [hq] at hkey
    exact hkey.symm
  · -- fixed unit ⟹ fixed conjugation
    have hc := hnorm (model.qEquiv.symm u.1)
    have hkey := model_qEquiv_conj model g (model.qEquiv.symm u.1) hc
    rw [MulEquiv.apply_symm_apply] at hkey
    rw [u.2] at hkey
    have heq : model.qEquiv ⟨(g : G') * ((model.qEquiv.symm u.1 : ↥hyp.Q) : G') *
        (g : G')⁻¹, hc⟩ = model.qEquiv (model.qEquiv.symm u.1) := by
      rw [MulEquiv.apply_symm_apply]; exact Units.ext hkey
    exact Subtype.ext_iff.mp (model.qEquiv.injective heq)

end ModelDAut

/-- **The fixed set of a ring automorphism of a finite field is a subfield**
(step (8), p. 110): for a finite field `F` of characteristic `f` and a ring
automorphism `σ`, the fixed set `{x : σ x = x}` is a subfield, hence has order
`f^a`.

The fixed set is the kernel of the additive endomorphism `σ − id` of `F`, hence
an additive subgroup, so its order divides `|F| = f^n` (additive Lagrange) and
is therefore a power of `f`. -/
theorem exists_card_fixedSet_eq_char_pow {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : f.Prime) [CharP F f] (σ : F ≃+* F) :
    ∃ a : ℕ, Nat.card {x : F // σ x = x} = f ^ a := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact f.Prime := ⟨hf⟩
  let A : AddSubgroup F :=
    { carrier := {x | σ x = x}
      add_mem' := fun {a b} ha hb => by
        have ha' : σ a = a := ha
        have hb' : σ b = b := hb
        change σ (a + b) = a + b
        rw [map_add, ha', hb']
      zero_mem' := show σ 0 = 0 from map_zero σ
      neg_mem' := fun {a} ha => by
        have ha' : σ a = a := ha
        change σ (-a) = -a
        rw [map_neg, ha'] }
  obtain ⟨n, -, hn⟩ := FiniteField.card F f
  have hdvd : Nat.card ↥A ∣ f ^ (n : ℕ) := by
    have hcard : Nat.card ↥A ∣ Nat.card F := AddSubgroup.card_addSubgroup_dvd_card A
    have hNF : Nat.card F = f ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
    rwa [hNF] at hcard
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hf).mp hdvd
  exact ⟨a, ha⟩

/-- **Step (8), the fixed-field order dichotomy** (p. 110): if the fixed *units*
of a ring automorphism `σ` of a finite field `F` (characteristic `f`) form a
group of order `2^b` with `b ≥ 1`, then the fixed field has order `f` or `9`.

The fixed field has order `f^a` (`exists_card_fixedSet_eq_char_pow`); its unit
group has order `f^a − 1 = 2^b`, so `f^a = 2^b + 1`, and the arithmetic lemma
`eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one` gives `f^a ∈ {f, 9}`. -/
theorem card_fixedSet_mem_of_units_two_pow {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : f.Prime) [CharP F f] (σ : F ≃+* F) {b : ℕ} (hb : 1 ≤ b)
    (hunits : Nat.card {x : F // σ x = x} = 2 ^ b + 1) :
    Nat.card {x : F // σ x = x} = f ∨ Nat.card {x : F // σ x = x} = 9 := by
  obtain ⟨a, ha⟩ := exists_card_fixedSet_eq_char_pow hf σ
  have heq : f ^ a = 2 ^ b + 1 := by rw [← ha]; exact hunits
  -- `f` is odd (else `f^a = 2^b + 1` odd would be even)
  have hfodd : Odd f := by
    rcases hf.eq_two_or_odd' with rfl | hodd
    · exfalso
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · simp only [pow_zero] at heq
        have hb1 : 1 ≤ (2 : ℕ) ^ b := Nat.one_le_two_pow
        omega
      · have h1 : (2 : ℕ) ∣ 2 ^ a := dvd_pow_self 2 hapos.ne'
        have h2 : (2 : ℕ) ∣ 2 ^ b := dvd_pow_self 2 (by omega : b ≠ 0)
        omega
    · exact hodd
  rcases eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one hfodd hb heq with ha1 | hf9
  · left; rw [ha, ha1, pow_one]
  · right; rw [ha]; exact hf9

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. II, step (8), `F` is a field** (p. 110, "By (5),
`F` is a field"): if `Q₁ ≠ 1` then the model's near-field `F` is commutative.

Step (5) (`card_nearField_eq_nine_and_Q1_eq_bot`) gives the dichotomy `F`
commutative, or `F ≅ F_{9,2}` with `Q₁ = 1`; the second alternative asserts
`Q₁ = 1`, so `Q₁ ≠ 1` leaves `F` commutative.

Inherits the step (2)(b) `sorry` (issue 9318) only through a model-supplying
caller, and the Higman `sorry` (step (5)). -/
theorem comm_of_Q1_ne_bot :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ∀ {F : Type uG} [NearFields.NearField F]
      (_model : NearFields.AffineNearFieldModel fc.rankOneQuotient F),
      fc.toHypothesis.Q1 ≠ ⊥ → ∀ x y : F, x * y = y * x := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  intro F instF _model hQ1 x y
  rcases fc.card_nearField_eq_nine_and_Q1_eq_bot _model with hcomm | ⟨_, _, hbot⟩
  · exact hcomm x y
  · exact absurd hbot hQ1

/-- **Peterfalvi Part II, Ch. II, step (8), the per-`w` induction facts**
(p. 110, "It follows from the induction hypothesis that `f = 3` or `5` and that
`C_Q(w)` is a `2`-group"): for a nonidentity `w ∈ C_W(P)`, applying §3
Proposition 1(c) to `X = ⟨w⟩` yields that the global product order
`f = |s·t|` is `3` or `5`, and `C_Q(w)` is a `2`-group.

`⟨w⟩ ≤ W ≤ V` is nontrivial, and `w` centralizes `Q₀` (so the four-subgroup of
`Q₀` lies in `C_G(w)`); the trichotomy reading
(`cQ_card_and_pGroup_of_trichotomy`) supplies both conclusions.

Inherits the step (2)(b) `sorry` (issue 9318) — none directly, this is a clean
application of the axiom-clean trichotomy reading. -/
theorem st_mem_and_cQ_isPGroup_of_mem_centralizer_W
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    {w : G} (hwW : w ∈ fc.toHypothesis.W)
    (_hwP : w ∈ Subgroup.centralizer (fc.P : Set G)) (hw1 : w ≠ 1) :
    (orderOf (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) = 3 ∨
        orderOf (fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t) = 5) ∧
      IsPGroup 2 ↥(fc.toHypothesis.Q.subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G))) := by
  set X : Subgroup G := Subgroup.zpowers w with hXdef
  have hwV : w ∈ fc.toHypothesis.V := fc.toHypothesis.W_le_V hwW
  have hXV : X ≤ fc.toHypothesis.V := (Subgroup.zpowers_le).mpr hwV
  have hX : X ≠ ⊥ := fun h => hw1 (Subgroup.zpowers_eq_bot.mp h)
  -- four-subgroup of `Q₀` sits in `C_G(⟨w⟩)`
  obtain ⟨E0, hE0Q0, hE04, hE0sq⟩ := fc.toHypothesis.exists_four_subgroup_le_Q0
  have hE0C : E0 ≤ Subgroup.centralizer (X : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcw : Commute w e := fc.W_mem_centralizes_Q0 hwW (hE0Q0 he)
    exact (hcw.zpow_left n).eq
  have hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
    refine ⟨E0.subgroupOf (Subgroup.centralizer (X : Set G)), ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE0C).toEquiv]; exact hE04
    · intro x hx
      exact Subtype.ext (by
        rw [Subgroup.coe_pow, hE0sq (x : G) (Subgroup.mem_subgroupOf.mp hx),
          Subgroup.coe_one])
  obtain ⟨hpg, hcases⟩ :=
    fc.toHypothesis.cQ_card_and_pGroup_of_trichotomy hXV hX hA3 ind
  refine ⟨?_, hpg⟩
  rcases hcases with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

/-- **The projection `C_Q(P) ≅ Q̄`** (step (8), reconstructing step (5)'s `ι`
without `qEquiv`): `mk' N` restricts to a group isomorphism from
`M₀ = Q ⊓ C_G(P)` onto the model's `Q̄`, whose value on `m` is `[m]`.

Injective because its kernel meets `Q ⊓ D = 1`; bijective because `|M₀| = |Q̄|`
(both equal `|F^*|`, via step (5)'s `C_Q(P) ≅ F^*` and `qEquiv`). -/
theorem exists_qbarEquiv {F : Type uG} [NearFields.NearField F]
    (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      NearFields.AffineNearFieldModel fc.rankOneQuotient F) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    ∃ e : ↥(fc.toHypothesis.Q ⊓ Subgroup.centralizer (fc.P : Set G)) ≃*
        ↥fc.rankOneQuotient.Q,
      ∀ m : ↥(fc.toHypothesis.Q ⊓ Subgroup.centralizer (fc.P : Set G)),
        ((e m : ↥fc.rankOneQuotient.Q) :
          ↥(Subgroup.centralizer (fc.P : Set G)) ⧸
            (fc.toHypothesis.H.subgroupOf
              (Subgroup.centralizer (fc.P : Set G))).normalCore) =
          QuotientGroup.mk' _ ⟨(m : G), m.2.2⟩ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hNdef
  set M₀ : Subgroup G := fc.toHypothesis.Q ⊓ L with hM₀def
  have hM₀L : M₀ ≤ L := inf_le_right
  have hQbar : fc.rankOneQuotient.Q =
      (fc.toHypothesis.Q.subgroupOf L).map (QuotientGroup.mk' N) := rfl
  have hmemQ : ∀ m : ↥M₀,
      ((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L)) m ∈
        fc.rankOneQuotient.Q := by
    intro m
    rw [hQbar]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr m.2.1)
  set piQ : ↥M₀ →* ↥fc.rankOneQuotient.Q :=
    ((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L)).codRestrict
      fc.rankOneQuotient.Q hmemQ with hpiQdef
  -- injective: kernel meets `Q ⊓ D = 1`
  have hpiQinj : Function.Injective piQ := by
    intro a b hab
    have h1 : ((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L))
        (a * b⁻¹) = 1 := by
      have h1' : piQ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
      exact congrArg Subtype.val h1'
    have h4 : Subgroup.inclusion hM₀L (a * b⁻¹) ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]; exact h1
    have h5 : Subgroup.inclusion hM₀L (a * b⁻¹) ∈ fc.toHypothesis.D.subgroupOf L := by
      have hND : N ≤ fc.toHypothesis.D.subgroupOf L := by
        rw [hNdef, fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
        exact inf_le_left
      exact hND h4
    have h6 : ((a * b⁻¹ : ↥M₀) : G) ∈ fc.toHypothesis.Q ⊓ fc.toHypothesis.D :=
      ⟨(a * b⁻¹).2.1, Subgroup.mem_subgroupOf.mp h5⟩
    rw [fc.toHypothesis.Q_inf_D_eq_bot, Subgroup.mem_bot] at h6
    exact mul_inv_eq_one.mp (Subtype.ext h6)
  -- `|M₀| = |Q̄|` (both `= |F^*|`)
  have hcard : Nat.card ↥M₀ = Nat.card ↥fc.rankOneQuotient.Q := by
    obtain ⟨e5⟩ := fc.centralizer_inf_mulEquiv_units model
    rw [Nat.card_congr e5.toEquiv, Nat.card_congr model.qEquiv.toEquiv]
  haveI : Finite ↥M₀ := inferInstance
  have hpiQbij : Function.Bijective piQ :=
    (Nat.bijective_iff_injective_and_card piQ).mpr ⟨hpiQinj, hcard⟩
  refine ⟨MulEquiv.ofBijective piQ hpiQbij, ?_⟩
  intro m
  rfl

/-- **The `[w]`-fixed elements of `Q̄` correspond to `C_Q(P) ∩ C_G(w)`**
(step (8), the equivariance transfer): for `w ∈ C_G(P) ∩ H`, the projection
`qbarEquiv` intertwines `w`-conjugation on `M₀ = C_Q(P)` with `[w]`-conjugation
on `Q̄`, so the two fixed-point counts agree. -/
theorem cardFixedConj_eq_cardFixedM0 {F : Type uG} [NearFields.NearField F]
    (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      NearFields.AffineNearFieldModel fc.rankOneQuotient F)
    {w : G} (hwL : w ∈ Subgroup.centralizer (fc.P : Set G))
    (hwH : w ∈ fc.toHypothesis.H) :
    letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    Nat.card {qb : ↥fc.rankOneQuotient.Q //
        QuotientGroup.mk'
            (fc.toHypothesis.H.subgroupOf
              (Subgroup.centralizer (fc.P : Set G))).normalCore ⟨w, hwL⟩ *
          (qb : _) *
          (QuotientGroup.mk'
            (fc.toHypothesis.H.subgroupOf
              (Subgroup.centralizer (fc.P : Set G))).normalCore ⟨w, hwL⟩)⁻¹ =
          (qb : _)} =
      Nat.card {m : ↥(fc.toHypothesis.Q ⊓ Subgroup.centralizer (fc.P : Set G)) //
        w * (m : G) * w⁻¹ = (m : G)} := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore with hNdef
  set M₀ : Subgroup G := fc.toHypothesis.Q ⊓ L with hM₀def
  set wbar := QuotientGroup.mk' N ⟨w, hwL⟩ with hwbar
  obtain ⟨e, he⟩ := fc.exists_qbarEquiv model
  have hstable : ∀ m : ↥M₀, w * (m : G) * w⁻¹ ∈ M₀ := fun m =>
    ⟨fc.toHypothesis.Q_normal_in_H w hwH (m : G) m.2.1,
      L.mul_mem (L.mul_mem hwL m.2.2) (L.inv_mem hwL)⟩
  -- equivariance: `[w q w⁻¹] = wbar · [q] · wbar⁻¹`
  have hequiv : ∀ m : ↥M₀,
      ((e ⟨w * (m : G) * w⁻¹, hstable m⟩ : ↥fc.rankOneQuotient.Q) : ↥L ⧸ N) =
        wbar * ((e m : ↥fc.rankOneQuotient.Q) : ↥L ⧸ N) * wbar⁻¹ := by
    intro m
    rw [he ⟨w * (m : G) * w⁻¹, hstable m⟩, he m, hwbar, ← map_inv, ← map_mul,
      ← map_mul]
    rfl
  -- the fixed conditions correspond under `e.symm`
  have hiff : ∀ qb : ↥fc.rankOneQuotient.Q,
      (wbar * (qb : ↥L ⧸ N) * wbar⁻¹ = (qb : ↥L ⧸ N)) ↔
        w * ((e.symm qb : ↥M₀) : G) * w⁻¹ = ((e.symm qb : ↥M₀) : G) := by
    intro qb
    have hem : e (e.symm qb) = qb := MulEquiv.apply_symm_apply e qb
    constructor
    · intro hq
      have h1 : ((e ⟨w * ((e.symm qb : ↥M₀) : G) * w⁻¹, hstable _⟩ :
          ↥fc.rankOneQuotient.Q) : ↥L ⧸ N) = ((e (e.symm qb) : ↥fc.rankOneQuotient.Q) :
          ↥L ⧸ N) := by rw [hequiv (e.symm qb), hem, hq]
      exact Subtype.ext_iff.mp (e.injective (Subtype.ext h1))
    · intro hm
      have h3 : (⟨w * ((e.symm qb : ↥M₀) : G) * w⁻¹, hstable _⟩ : ↥M₀) = e.symm qb :=
        Subtype.ext hm
      calc wbar * (qb : ↥L ⧸ N) * wbar⁻¹
          = wbar * ((e (e.symm qb) : ↥fc.rankOneQuotient.Q) : ↥L ⧸ N) * wbar⁻¹ := by
            rw [hem]
        _ = ((e ⟨w * ((e.symm qb : ↥M₀) : G) * w⁻¹, hstable _⟩ :
              ↥fc.rankOneQuotient.Q) : ↥L ⧸ N) := (hequiv (e.symm qb)).symm
        _ = ((e (e.symm qb) : ↥fc.rankOneQuotient.Q) : ↥L ⧸ N) := by rw [h3]
        _ = (qb : ↥L ⧸ N) := by rw [hem]
  exact Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv hiff)

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
