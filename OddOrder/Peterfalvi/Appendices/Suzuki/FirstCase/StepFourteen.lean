/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepThirteen

/-!
# Peterfalvi Part II, Ch. II, step (14): the centre of `RΣ`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (14), p. 113.

In the notation of (11) (`R` the preimage of the near-field `F`, `T = [R, s]`,
`Σ = C_W(P)`, `Z₁ = ⟨st⟩`):

* `Z₁P ≤ Z(RΣ)`: `R` is abelian and contains both `Z₁` (by the "`Z₁ ⊂ T`"
  remark) and `P`; and `Σ` centralizes `P` by definition, while `Σ ≤ W ≤ V`
  centralizes both `s` (Ch. I Prop 5) and `t` (definition of `V`), hence `st`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace OddOrder.Peterfalvi.Appendices.Suzuki

section GenericCentre

variable {G' : Type*} [Group G'] [Finite G']

omit [Finite G'] in
/-- `|A ⊔ B| = |A|·|B|` for two elementwise commuting subgroups meeting trivially. -/
theorem card_sup_eq_mul_of_commute {A B : Subgroup G'}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  classical
  have hcoe : ((A ⊔ B : Subgroup G') : Set G') = (A : Set G') * (B : Set G') := by
    refine Subgroup.coe_mul_of_right_le_normalizer_left _ _ ?_
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have h1 : b * a * b⁻¹ = a := by
        rw [← hcomm a ha b hb]; group
      rw [h1]; exact ha
    · intro ha
      have h1 : (b * a * b⁻¹) * b = b * (b * a * b⁻¹) := hcomm _ ha b hb
      have h2 : b * a = b * (b * a * b⁻¹) := by rw [← h1]; group
      have h3 : a = b * a * b⁻¹ := mul_left_cancel h2
      rw [h3]; exact ha
  have hmul : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
    intro x hx
    have hx' : x ∈ ((A : Set G') * (B : Set G')) := by rw [← hcoe]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  have hbot : B ⊓ A = ⊥ := by rw [inf_comm]; exact hinf
  have hcompl := (Subgroup.isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    (le_sup_right : B ≤ A ⊔ B) (le_sup_left : A ≤ A ⊔ B) hbot hmul).card_mul
  have hAc : Nat.card ↥(A.subgroupOf (A ⊔ B)) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hBc : Nat.card ↥(B.subgroupOf (A ⊔ B)) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [← hAc, ← hBc]
  exact hcompl.symm

omit [Finite G'] in
/-- The centre of a subgroup `K`, computed inside `K`, is `(K ⊓ C_G(K))` transported
along `subgroupOf`. -/
theorem center_eq_inf_centralizer_subgroupOf (K : Subgroup G') :
    Subgroup.center ↥K = (K ⊓ Subgroup.centralizer (K : Set G')).subgroupOf K := by
  ext x
  rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    intro g hg
    have := h ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rintro ⟨-, h2⟩ y
    exact Subtype.ext (h2 (y : G') y.2)

/-- **A `p²`-index central subgroup of a nonabelian group is the whole centre.**
If `Z ≤ Z(K)` has index `p²` (`p` prime) and `K` is nonabelian, then the centre
cannot be larger: index `1` or `p` would make `K/Z(K)` cyclic. -/
theorem inf_centralizer_eq_of_index_sq_of_not_comm {K Z : Subgroup G'} {p : ℕ}
    (hp : p.Prime) (hZ : Z ≤ K ⊓ Subgroup.centralizer (K : Set G'))
    (hcard : Nat.card ↥K = p ^ 2 * Nat.card ↥Z)
    (hnc : ¬ ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) :
    K ⊓ Subgroup.centralizer (K : Set G') = Z := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G' := K ⊓ Subgroup.centralizer (K : Set G') with hC_def
  have hCK : C ≤ K := inf_le_left
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hZ
  set b := (C.subgroupOf K).index with hb_def
  have hlag : Nat.card ↥C * b = Nat.card ↥K := by
    have h := (C.subgroupOf K).card_mul_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv] at h
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hab : a * b = p ^ 2 := by
    have h1 : Nat.card ↥Z * (a * b) = Nat.card ↥Z * p ^ 2 := by
      rw [← mul_assoc, ← ha, hlag, hcard]; ring
    exact Nat.eq_of_mul_eq_mul_left hZpos h1
  -- the quotient `K/Z(K)` has order `b`, and it is not cyclic
  have hZidx : Subgroup.center ↥K = C.subgroupOf K :=
    center_eq_inf_centralizer_subgroupOf K
  have hcardq : Nat.card (↥K ⧸ Subgroup.center ↥K) = b := by
    rw [hZidx, hb_def, Subgroup.index_eq_card]
  have hnotcyc : ¬ IsCyclic (↥K ⧸ Subgroup.center ↥K) := by
    intro hcyc
    refine hnc ?_
    have hcomm : IsMulCommutative ↥K :=
      MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (Subgroup.center ↥K)) (by rw [QuotientGroup.ker_mk'])
    intro x hx y hy
    exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : ↥K) ⟨y, hy⟩)
  have hb1 : b ≠ 1 := by
    intro h
    apply hnotcyc
    haveI : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by
      have h0 : Nat.card (↥K ⧸ Subgroup.center ↥K) = 1 := by rw [hcardq, h]
      exact (Nat.card_eq_one_iff_unique.mp h0).1
    exact isCyclic_of_subsingleton
  have hbp : b ≠ p := fun h =>
    hnotcyc (isCyclic_of_prime_card (p := p) (by rw [hcardq, h]))
  -- `b ∣ p²` with `b ∉ {1, p}` forces `b = p²`, hence `a = 1`
  have hbdvd : b ∣ p ^ 2 := ⟨a, by rw [← hab]; ring⟩
  obtain ⟨i, hi2, hi⟩ := (Nat.dvd_prime_pow hp).mp hbdvd
  have hi_eq : i = 2 := by
    interval_cases i
    · exact absurd (by rw [hi, pow_zero] : b = 1) hb1
    · exact absurd (by rw [hi, pow_one] : b = p) hbp
    · rfl
  have ha1 : a = 1 := by
    rw [hi_eq] at hi
    rw [hi] at hab
    have hppos : 0 < p ^ 2 := pow_pos hp.pos 2
    have h4 : a * p ^ 2 = 1 * p ^ 2 := by rw [one_mul]; exact hab
    exact Nat.eq_of_mul_eq_mul_right hppos h4
  have hCZ : Nat.card ↥C = Nat.card ↥Z := by rw [ha, ha1, mul_one]
  exact (Subgroup.eq_of_le_of_card_ge hZ (le_of_eq hCZ)).symm

end GenericCentre

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

include fc in
/-- `Σ = C_W(P)` centralizes the distinguished involution `s`: `Σ ≤ W ≤ V` and
`V = C_D(s)` (Ch. I Prop 5). -/
lemma centralizer_W_le_centralizer_distinguishedInvolution :
    fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)
      ≤ Subgroup.centralizer
        ({fc.toHypothesis.distinguishedInvolution} : Set G) := by
  intro w hw
  have hwV : w ∈ fc.toHypothesis.V := fc.toHypothesis.W_le_V hw.1
  exact (fc.toHypothesis.V_le_centralizer_distinguishedInvolution hwV).2

include fc in
/-- `Σ` centralizes `st`: it centralizes `s` (above) and `t` (as `Σ ≤ V = C_D(t)`). -/
lemma centralizer_W_le_centralizer_distinguishedInvolution_mul_t :
    fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)
      ≤ Subgroup.centralizer
        ({fc.toHypothesis.distinguishedInvolution * fc.toHypothesis.t}
          : Set G) := by
  intro w hw
  have hws : Commute w fc.toHypothesis.distinguishedInvolution :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (fc.centralizer_W_le_centralizer_distinguishedInvolution hw)
  have hwt : Commute w fc.toHypothesis.t :=
    fc.toHypothesis.commute_t_of_mem_V (fc.toHypothesis.W_le_V hw.1)
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hws.mul_right hwt)

include model in
/-- **`Z₁P ≤ Z(RΣ)`** ((14), p. 113; the centre is taken inside `G`, i.e. as
`RΣ ⊓ C_G(RΣ)`).

`Z₁ ≤ T ≤ R` and `P ≤ R` with `R` abelian, so `Z₁P` centralizes `R`; and `Σ`
centralizes `P` by definition and `st` because `Σ ≤ V = C_D(s) = C_D(t)`. -/
theorem zpowers_mul_t_sup_P_le_center_sup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {m : ℕ}
    (hm : Nat.card F = fc.p ^ m) :
    Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) ⊔ fc.P
      ≤ (fc.invImageF model
            ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
        ⊓ Subgroup.centralizer
          (((fc.invImageF model
            ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
              : Subgroup G) : Set G) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set R : Subgroup G := fc.invImageF model with hR_def
  set Sg : Subgroup G :=
    fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G) with hSg_def
  have hZ₁R : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ≤ R :=
    (fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm).trans
      (fc.sInvertedT_spec model ind hB2 hm).1
  have hPR : fc.P ≤ R := fc.P_le_invImageF model
  have habR := fc.invImageF_mul_comm model ind hB2 hm
  -- both generators of `Z₁P` centralize `R` and `Σ`
  have hcent : ∀ z ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ⊔ fc.P, z ∈ Subgroup.centralizer ((R ⊔ Sg : Subgroup G) : Set G) := by
    intro z hz
    have hzR : z ∈ R := sup_le hZ₁R hPR hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    -- `x = r·σ` with `r ∈ R`, `σ ∈ Σ`
    have hx' : x ∈ ((R : Set G) * (Sg : Set G)) := by
      rw [← fc.coe_sup_invImageF_centralizer_W model]
      exact hx
    obtain ⟨r, hr, w, hw, rfl⟩ := hx'
    -- `z` commutes with `r` (both in the abelian `R`)
    have hzr : z * r = r * z := habR z hzR r hr
    -- `z` commutes with `w ∈ Σ`
    have hzw : z * w = w * z := by
      have hzcw : z ∈ Subgroup.centralizer (Sg : Set G) := by
        refine (sup_le ?_ ?_ : Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t) ⊔ fc.P ≤ Subgroup.centralizer (Sg : Set G)) hz
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro y hy
          exact Subgroup.mem_centralizer_singleton_iff.mp
            (fc.centralizer_W_le_centralizer_distinguishedInvolution_mul_t hy)
        · intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          exact (Subgroup.mem_centralizer_iff.mp hc.2 y hy).symm
      exact (Subgroup.mem_centralizer_iff.mp hzcw w hw).symm
    calc r * w * z = r * (w * z) := by group
      _ = r * (z * w) := by rw [hzw]
      _ = (r * z) * w := by group
      _ = (z * r) * w := by rw [hzr]
      _ = z * (r * w) := by group
  refine le_inf ?_ (fun z hz => hcent z hz)
  exact sup_le (hZ₁R.trans le_sup_left) (hPR.trans le_sup_left)

include model in
/-- **Peterfalvi Part II, Ch. II, step (14), first assertion** (p. 113):
`Z(RΣ) = Z₁P`, with the centre taken inside `G` as `RΣ ⊓ C_G(RΣ)`.

In case (10.2) (which holds by step (12)) we have `p = 3`, `|F| = 9`, `|Σ| = 3`,
so `|R| = |F|·|P| = 27` and `|RΣ| = 81`, while `|Z₁P| = |Z₁|·|P| = 9` (the two
factors commute inside the abelian `R` and meet trivially since `Z₁ ≤ T` and
`T ⊓ P = 1`).  Thus `Z₁P` has index `3²` in `RΣ`, and `RΣ` is nonabelian because
a nonidentity element of `Σ` fails to centralize `R`; the centre can therefore be
no larger than `Z₁P`. -/
theorem inf_centralizer_sup_eq_zpowers_sup_P
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    (fc.invImageF model
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
        ⊓ Subgroup.centralizer
          (((fc.invImageF model
            ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
              : Subgroup G) : Set G)
      = Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t) ⊔ fc.P := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  -- case (10.2) numerics
  obtain ⟨hpSig, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  obtain ⟨-, -, -, hSig3, -⟩ :=
    fc.card_field_eq_nine_of_p_dvd_card_centralizer_W ind model hB2 hpSig
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  set R : Subgroup G := fc.invImageF model with hR_def
  set Sg : Subgroup G :=
    fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G) with hSg_def
  set Z₁ : Subgroup G := Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
    * fc.toHypothesis.t) with hZ₁_def
  -- `|R| = 27` and `|RΣ| = 81`
  have hPcard : Nat.card ↥fc.P = 3 := by rw [fc.card_P, hp3]
  have hRcard : Nat.card ↥R = 27 := by
    rw [hR_def, fc.card_invImageF model ind, hF9, hPcard]
  have hRScard : Nat.card ↥(R ⊔ Sg) = 81 := by
    rw [hR_def, hSg_def, fc.card_sup_invImageF_centralizer_W model ind]
    rw [← hR_def, ← hSg_def, hRcard, hSig3]
  -- `|Z₁| = 3` and `Z₁ ⊓ P = 1`, so `|Z₁P| = 9`
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  have hZ₁card : Nat.card ↥Z₁ = 3 := by rw [hZ₁_def, Nat.card_zpowers, hstord]
  have hZ₁T : Z₁ ≤ fc.sInvertedT model :=
    fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm
  have hTP : fc.sInvertedT model ⊓ fc.P = ⊥ :=
    (fc.sInvertedT_spec model ind hB2 hm).2.2.2
  have hZ₁P : Z₁ ⊓ fc.P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ fc.sInvertedT model ⊓ fc.P := ⟨hZ₁T hx.1, hx.2⟩
    rwa [hTP] at this
  have habR := fc.invImageF_mul_comm model ind hB2 hm
  have hZ₁R : Z₁ ≤ R := hZ₁T.trans (fc.sInvertedT_spec model ind hB2 hm).1
  have hPR : fc.P ≤ R := fc.P_le_invImageF model
  have hcomm : ∀ a ∈ Z₁, ∀ b ∈ fc.P, a * b = b * a := fun a ha b hb =>
    habR a (hZ₁R ha) b (hPR hb)
  have hZ₁Pcard : Nat.card ↥(Z₁ ⊔ fc.P) = 9 := by
    rw [card_sup_eq_mul_of_commute hcomm hZ₁P, hZ₁card, hPcard]
  -- `RΣ` is nonabelian: a nonidentity element of `Σ` does not centralize `R`
  have hSgne : Sg ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hSig3
    omega
  obtain ⟨w, hwSg, hw1⟩ : ∃ w ∈ Sg, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hSgne (by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact hcon x hx)
  have hnc : ¬ ∀ x ∈ R ⊔ Sg, ∀ y ∈ R ⊔ Sg, x * y = y * x := by
    intro hcomm'
    refine fc.not_forall_comm_of_mem_centralizer_W model ind hwSg.1 hwSg.2 hw1 ?_
    intro r hr
    exact hcomm' w ((le_sup_right : Sg ≤ R ⊔ Sg) hwSg) r
      ((le_sup_left : R ≤ R ⊔ Sg) hr)
  -- assemble
  refine inf_centralizer_eq_of_index_sq_of_not_comm (p := 3) (by norm_num) ?_ ?_ hnc
  · exact fc.zpowers_mul_t_sup_P_le_center_sup model ind hB2 hm
  · rw [hRScard, hZ₁Pcard]
    norm_num

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
