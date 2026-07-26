/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_FrobeniusBasics

/-!
# BG Appendix C, Lemma C.3: the transported configuration

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, §3 (pp. 148--152).

Under hypothesis (B) the monomorphism `σ : H = P ⋊ U → G` transports the concrete Frobenius
group into `G`.  This file develops the resulting configuration inside `G`: the distinguished
element `s = σ(1) ∈ σ(P₀)`, the isomorphism `U ≅ σ(U)`, the decomposition `σ(H) = PU` with
`P ∩ U = 1`, the fact that `P` is characteristic in `PU` (`p`-torsion lands in `P`), the
irreducibility bridge for subgroups between `U` and `PU`, and Steps 1--2 of Lemma C.3 read
through `σ`.  It culminates in `s_not_normalizes_U`, the contradiction that drives Step 4.

Everything here is stated against the book's abstract hypotheses
(`OddOrder.BG.AppC.FieldNormalizerData` = (A) + (B)); nothing refers to the Peterfalvi Section 16
configuration, which supplies one instance of (B) along the Feit--Thompson spine (issue 0151).
-/

namespace OddOrder.BG.AppC

open scoped Pointwise

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- The BG element `s ∈ P₀#`, transported to `G` through the concrete
field-normalizer monomorphism. -/
noncomputable def s (data : FieldNormalizerData p q G) : G :=
  data.sigma (primeLineGenerator p q)

/-- The transported element `s` lies in Peterfalvi's subgroup `W₂ = σ(P₀)`. -/
theorem s_mem_W2 (data : FieldNormalizerData p q G) :
    data.s ∈ data.W2 := by
  rw [← data.sigma_P0_eq_W2]
  exact ⟨primeLineGenerator p q,
    primeLineGenerator_mem p q, rfl⟩

/-- The transported element `s` lies in the transported additive kernel `P`. -/
theorem s_mem_P (data : FieldNormalizerData p q G) :
    data.s ∈ data.P := by
  rw [← data.sigma_P_eq_P]
  refine ⟨primeLineGenerator p q, ?_, rfl⟩
  dsimp [primeLineGenerator, NormSet.normOneFrobeniusKernel]
  exact ⟨Multiplicative.ofAdd (1 : GaloisField p q), rfl⟩

/-- Integer powers of `s` remain in `P`. -/
theorem s_zpow_mem_P (data : FieldNormalizerData p q G)
    (n : ℤ) :
    data.s ^ n ∈ data.P :=
  data.P.zpow_mem data.s_mem_P n

/-- Integer powers of `s` lie in `PU`. -/
theorem s_zpow_mem_P_sup_U (data : FieldNormalizerData p q G) (n : ℤ) :
    data.s ^ n ∈ data.P ⊔ data.U :=
  (le_sup_left : data.P ≤ data.P ⊔ data.U) (data.s_zpow_mem_P n)

/-- Integer powers of the transported generator `s` are exactly the corresponding
points of the concrete prime-field line. -/
theorem s_zpow_eq_primeLineElement (data : FieldNormalizerData p q G) (n : ℤ) :
    data.s ^ n =
      data.sigma (primeLineElement p q (n : ZMod p)) := by
  calc
    data.s ^ n = data.sigma ((primeLineGenerator p q) ^ n) := by
      rw [s, map_zpow]
    _ = data.sigma (primeLineElement p q (n : ZMod p)) := by
      congr 1
      dsimp [primeLineElement, primeLineGenerator]
      rw [← map_zpow (SemidirectProduct.inl :
        NormSet.additiveFieldGroup p q →*
          NormSet.normOneFrobeniusGroup p q)]
      rw [SemidirectProduct.inl_inj]
      rw [← ofAdd_zsmul]
      congr 1
      simp [zsmul_eq_mul]

/-- The `s^{-2}` factor in BG C.3 Step 4 is the `-2` point of the concrete
prime-field line after transport by `σ`. -/
theorem s_zpow_neg_two_eq_primeLineElement_neg_two
    (data : FieldNormalizerData p q G) :
    data.s ^ (-2 : ℤ) =
      data.sigma (primeLineElement p q (-2 : ZMod p)) := by
  dsimp [s, primeLineElement, primeLineGenerator]
  let F := GaloisField p q
  let H := NormSet.normOneFrobeniusGroup p q
  have hpow_two :
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) ^ 2 =
        SemidirectProduct.inl (Multiplicative.ofAdd (2 : F)) := by
    rw [pow_two, ← map_mul (SemidirectProduct.inl :
      NormSet.additiveFieldGroup p q →* H)]
    congr
    apply Multiplicative.toAdd.injective
    change (1 : F) + 1 = 2
    ring
  have hneg_two :
      (algebraMap (ZMod p) F (-2 : ZMod p)) = -(2 : F) := by
    simp only [map_neg, map_ofNat]
  rw [← map_zpow]
  congr
  rw [zpow_neg, hneg_two]
  change ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) ^ 2)⁻¹ =
    SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))
  have hpow_two_inv := congrArg Inv.inv hpow_two
  exact hpow_two_inv.trans (by simp [F])

/-- The transported element `s` is nontrivial. -/
theorem s_ne_one (data : FieldNormalizerData p q G) :
    data.s ≠ 1 := by
  intro hs
  exact primeLineGenerator_ne_one p q
    (data.sigma_injective (by simpa [s] using hs))

/-- The transported prime-line generator has `p`-th power equal to `1`. -/
theorem s_pow_p_eq_one (data : FieldNormalizerData p q G) :
    data.s ^ p = 1 := by
  simpa [s] using congrArg data.sigma (primeLineGenerator_pow_p p q)

/-- The transported generator `s` has exact order `p`. -/
theorem s_orderOf_eq_p (data : FieldNormalizerData p q G) :
    orderOf data.s = p := by
  have hdiv : orderOf data.s ∣ p :=
    orderOf_dvd_of_pow_eq_one data.s_pow_p_eq_one
  rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (orderOf data.s) hdiv with h | h
  · exact False.elim (data.s_ne_one (orderOf_eq_one_iff.mp h))
  · exact h

/-- The transported prime line `W₂ = σ(P₀)` is generated by the distinguished
nonidentity element `s`.  This is the `P₀ = ⟨s⟩` input in BG Appendix C. -/
theorem W2_eq_zpowers_s (data : FieldNormalizerData p q G) :
    data.W2 = Subgroup.zpowers data.s := by
  have hsle : Subgroup.zpowers data.s ≤ data.W2 :=
    Subgroup.zpowers_le.mpr data.s_mem_W2
  haveI : Finite data.W2 := Nat.finite_of_card_ne_zero (by
    rw [data.card_W2]
    exact (Fact.out : Nat.Prime p).ne_zero)
  have hcard : Nat.card ↥data.W2 ≤ Nat.card ↥(Subgroup.zpowers data.s) := by
    rw [Nat.card_zpowers, data.s_orderOf_eq_p, data.card_W2]
  exact (Subgroup.eq_of_le_of_card_ge hsle hcard).symm

/-- The transported prime line `W₂ = σ(P₀)` lies in Peterfalvi's additive kernel
`P`. -/
theorem W2_le_P (data : FieldNormalizerData p q G) :
    data.W2 ≤ data.P := by
  rw [data.W2_eq_zpowers_s]
  exact Subgroup.zpowers_le.mpr data.s_mem_P

/-- The transported prime line `W₂ = σ(P₀)` is a `p`-group of order `p`. -/
theorem W2_isPGroup (data : FieldNormalizerData p q G) :
    IsPGroup p data.W2 := by
  haveI : Finite data.W2 := Nat.finite_of_card_ne_zero (by
    rw [data.card_W2]
    exact (Fact.out : Nat.Prime p).ne_zero)
  rw [IsPGroup.iff_card]
  exact ⟨1, by rw [pow_one]; exact data.card_W2⟩

/-- The transported prime-line generator normalizes `Q`. -/
theorem s_normalizes_Q (data : FieldNormalizerData p q G) :
    data.s ∈ Subgroup.normalizer (data.Q : Set G) :=
  data.W2_normalizes_Q data.s_mem_W2

/-- The concrete norm-one complement transported through `σ` onto Peterfalvi's
subgroup `U`. -/
noncomputable def normOneUnitsToU (data : FieldNormalizerData p q G) :
    NormSet.normOneUnits p q →* data.U :=
  { toFun := fun u =>
      ⟨data.sigma (SemidirectProduct.inr u), by
        rw [← data.sigma_U_eq_U]
        exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩⟩
    map_one' := by
      ext
      simp
    map_mul' := by
      intro u v
      ext
      simp }

/-- The transported norm-one complement map is injective. -/
theorem normOneUnitsToU_injective (data : FieldNormalizerData p q G) :
    Function.Injective data.normOneUnitsToU := by
  intro u v h
  have hsig : data.sigma (SemidirectProduct.inr u) = data.sigma (SemidirectProduct.inr v) :=
    congrArg Subtype.val h
  exact SemidirectProduct.inr_injective (data.sigma_injective hsig)

/-- The transported norm-one complement map is onto Peterfalvi's `U`. -/
theorem normOneUnitsToU_surjective (data : FieldNormalizerData p q G) :
    Function.Surjective data.normOneUnitsToU := by
  intro u
  have hu : (u : G) ∈ (NormSet.normOneFrobeniusComplement p q).map data.sigma := by
    rw [data.sigma_U_eq_U]
    exact u.property
  rcases hu with ⟨x, hxU, hx⟩
  rcases hxU with ⟨u0, rfl⟩
  refine ⟨u0, ?_⟩
  ext
  exact hx

/-- The concrete norm-one unit group is isomorphic to Peterfalvi's subgroup `U`
through the field-normalizer embedding. -/
noncomputable def normOneUnitsEquivU (data : FieldNormalizerData p q G) :
    NormSet.normOneUnits p q ≃* data.U :=
  MulEquiv.ofBijective data.normOneUnitsToU
    ⟨data.normOneUnitsToU_injective, data.normOneUnitsToU_surjective⟩

/-- The transported additive kernel `P` and complement `U` meet trivially in
`G`.  This is the S16-facing form of the `U ∩ P = 1` input used when BG
Appendix C, Lemma C.3 Step 4 reads equations modulo `P`. -/
theorem P_inf_U_eq_bot (data : FieldNormalizerData p q G) :
    data.P ⊓ data.U = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxP : x ∈ (NormSet.normOneFrobeniusKernel p q).map data.sigma := by
    rw [data.sigma_P_eq_P]
    exact hx.1
  have hxU : x ∈ (NormSet.normOneFrobeniusComplement p q).map data.sigma := by
    rw [data.sigma_U_eq_U]
    exact hx.2
  rcases hxP with ⟨a, hpP, hp⟩
  rcases hxU with ⟨u, huU, hu⟩
  have hpu : a = u := data.sigma_injective (by
    rw [hp, hu])
  have hp_inter :
      a ∈ NormSet.normOneFrobeniusKernel p q ⊓ NormSet.normOneFrobeniusComplement p q := by
    exact ⟨hpP, by rwa [hpu]⟩
  have hp_one : a = 1 := by
    have hp_bot : a ∈ (⊥ : Subgroup (NormSet.normOneFrobeniusGroup p q)) := by
      rw [← normOneFrobeniusKernel_inf_complement_eq_bot p q]
      exact hp_inter
    simpa [Subgroup.mem_bot] using hp_bot
  rw [Subgroup.mem_bot]
  rw [← hp, hp_one, map_one]

/-- The image of the concrete Frobenius group is the subgroup generated by the
transported additive kernel `P` and complement `U`. -/
theorem P_sup_U_eq_sigma_top (data : FieldNormalizerData p q G) :
    data.P ⊔ data.U =
      (⊤ : Subgroup (NormSet.normOneFrobeniusGroup p q)).map data.sigma := by
  calc
    data.P ⊔ data.U =
        (NormSet.normOneFrobeniusKernel p q).map data.sigma ⊔
          (NormSet.normOneFrobeniusComplement p q).map data.sigma := by
      rw [data.sigma_P_eq_P, data.sigma_U_eq_U]
    _ = (NormSet.normOneFrobeniusKernel p q ⊔
          NormSet.normOneFrobeniusComplement p q).map data.sigma := by
      rw [Subgroup.map_sup]
    _ = (⊤ : Subgroup (NormSet.normOneFrobeniusGroup p q)).map data.sigma := by
      rw [normOneFrobeniusKernel_sup_complement_eq_top p q]


/-- Transported form: every element of Peterfalvi's `P` has `p`-th power `1`. -/
theorem P_pow_p_eq_one (data : FieldNormalizerData p q G)
    {x : G} (hx : x ∈ data.P) :
    x ^ p = 1 := by
  rw [← data.sigma_P_eq_P] at hx
  rcases hx with ⟨h, hhK, hh⟩
  have hhpow := normOneFrobeniusKernel_pow_p_eq_one p q hhK
  calc
    x ^ p = (data.sigma h) ^ p := by rw [hh]
    _ = data.sigma (h ^ p) := by rw [map_pow]
    _ = 1 := by rw [hhpow, map_one]

/-- Transported form of `P char PU`: the `p`-torsion in `PU` lies in `P`. -/
theorem mem_P_of_mem_P_sup_U_of_pow_p_eq_one
    (data : FieldNormalizerData p q G)
    {x : G} (hxPU : x ∈ data.P ⊔ data.U) (hxp : x ^ p = 1) :
    x ∈ data.P := by
  have hxrange : x ∈ (⊤ : Subgroup (NormSet.normOneFrobeniusGroup p q)).map data.sigma := by
    rwa [← data.P_sup_U_eq_sigma_top]
  rcases hxrange with ⟨h, _hhtop, hh⟩
  have hhp : h ^ p = 1 := data.sigma_injective (by
    calc
      data.sigma (h ^ p) = (data.sigma h) ^ p := by rw [map_pow]
      _ = x ^ p := by rw [hh]
      _ = 1 := hxp
      _ = data.sigma 1 := by rw [map_one])
  have hhK := normOneFrobeniusGroup_mem_kernel_of_pow_p_eq_one p q data.q_prime.ne_zero h hhp
  rw [← data.sigma_P_eq_P]
  exact ⟨h, hhK, hh⟩

/-- BG Appendix C Step 3, `P char PU` in normalizer form: anything normalizing
`PU` also normalizes its additive kernel `P`. -/
theorem normalizer_P_sup_U_le_normalizer_P
    (data : FieldNormalizerData p q G) :
    Subgroup.normalizer ((data.P ⊔ data.U : Subgroup G) : Set G) ≤
      Subgroup.normalizer (data.P : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hxP
    have hxPU : x ∈ data.P ⊔ data.U := (le_sup_left : data.P ≤
      data.P ⊔ data.U) hxP
    have hconjPU : g * x * g⁻¹ ∈ data.P ⊔ data.U := (hg x).mp hxPU
    have hxpow : x ^ p = 1 := data.P_pow_p_eq_one hxP
    have hconjpow : (g * x * g⁻¹) ^ p = 1 := by
      have h := congrArg (MulAut.conj g) hxpow
      rw [map_pow] at h
      simpa [MulAut.conj_apply] using h
    exact data.mem_P_of_mem_P_sup_U_of_pow_p_eq_one hconjPU hconjpow
  · intro hxconjP
    have hconjPU : g * x * g⁻¹ ∈ data.P ⊔ data.U :=
      (le_sup_left : data.P ≤ data.P ⊔ data.U) hxconjP
    have hxPU : x ∈ data.P ⊔ data.U := (hg x).mpr hconjPU
    have hconjpow : (g * x * g⁻¹) ^ p = 1 := data.P_pow_p_eq_one hxconjP
    have hxpow : x ^ p = 1 := by
      have h := congrArg (MulAut.conj g⁻¹) hconjpow
      rw [map_pow] at h
      have hback : MulAut.conj g⁻¹ (g * x * g⁻¹) = x := by
        simp
        group
      rw [hback] at h
      simpa [MulAut.conj_apply] using h
    exact data.mem_P_of_mem_P_sup_U_of_pow_p_eq_one hxPU hxpow

/-- BG Appendix C, Lemma C.3 Step 3 irreducibility bridge: any subgroup of
`PU` that contains `U` is either `U` or all of `PU`.  This transports the
concrete irreducibility theorem for `P⋊U` through `σ`. -/
theorem subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U
    (data : FieldNormalizerData p q G) {X : Subgroup G}
    (hUle : data.U ≤ X) (hXle : X ≤ data.P ⊔ data.U)
    (hne : X ≠ data.U) :
    X = data.P ⊔ data.U := by
  let XH : Subgroup (NormSet.normOneFrobeniusGroup p q) := X.comap data.sigma
  have hXrange : X ≤ data.sigma.range := by
    intro x hx
    have hxPU : x ∈ data.P ⊔ data.U := hXle hx
    rw [data.P_sup_U_eq_sigma_top] at hxPU
    simpa using hxPU
  have hUleH : NormSet.normOneFrobeniusComplement p q ≤ XH := by
    intro g hg
    have hgU : data.sigma g ∈ data.U := by
      rw [← data.sigma_U_eq_U]
      exact ⟨g, hg, rfl⟩
    exact hUle hgU
  have hUleH' :
      (SemidirectProduct.inr : NormSet.normOneUnits p q →*
        NormSet.normOneFrobeniusGroup p q).range ≤ XH := by
    simpa [NormSet.normOneFrobeniusComplement,
      NormSet.normOneFrobeniusComplement] using hUleH
  have hneH : XH ≠ NormSet.normOneFrobeniusComplement p q := by
    intro hXH
    apply hne
    have hmapX : XH.map data.sigma = X := Subgroup.map_comap_eq_self hXrange
    calc
      X = XH.map data.sigma := hmapX.symm
      _ = (NormSet.normOneFrobeniusComplement p q).map data.sigma := by rw [hXH]
      _ = data.U := data.sigma_U_eq_U
  have htopH : XH = ⊤ :=
    NormSet.normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_ne_inr_range
      (p := p) (q := q) data.q_prime data.cyclotomic_coprime
      XH hUleH'
      (by simpa [NormSet.normOneFrobeniusComplement,
        NormSet.normOneFrobeniusComplement] using hneH)
  have hmapX : XH.map data.sigma = X := Subgroup.map_comap_eq_self hXrange
  calc
    X = XH.map data.sigma := hmapX.symm
    _ = (⊤ : Subgroup (NormSet.normOneFrobeniusGroup p q)).map data.sigma := by rw [htopH]
    _ = data.P ⊔ data.U := data.P_sup_U_eq_sigma_top.symm

/-- BG Appendix C, Lemma C.3 Step 1 inside the concrete `P⋊U`: every element is
`u s₁ v` with `u,v∈U` and `s₁∈P₀`. -/
theorem exists_normOne_primeLine_normOne (data : FieldNormalizerData p q G)
    (g : NormSet.normOneFrobeniusGroup p q) :
    ∃ c : ZMod p, ∃ u v : NormSet.normOneUnits p q,
      g = (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        primeLineElement p q c * SemidirectProduct.inr v := by
  simpa [primeLineElement] using
    NormSet.normOneFrobenius_exists_inr_primeLine_inr
      (p := p) (q := q) data.q_prime data.cyclotomic_coprime
      (s := (1 : GaloisField p q)) one_ne_zero g

/-- BG Appendix C, Lemma C.3 Step 1 transported to `G`: every element of `PU`
can be written as the `σ`-image of `u s₁ v`. -/
theorem exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data : FieldNormalizerData p q G)
    {x : G} (hx : x ∈ data.P ⊔ data.U) :
    ∃ c : ZMod p, ∃ u v : NormSet.normOneUnits p q,
      x = data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v : NormSet.normOneFrobeniusGroup p q) := by
  have hxmap : x ∈ (⊤ : Subgroup (NormSet.normOneFrobeniusGroup p q)).map data.sigma := by
    rw [← data.P_sup_U_eq_sigma_top]
    exact hx
  rcases hxmap with ⟨g, _hg_top, hg⟩
  rcases data.exists_normOne_primeLine_normOne g with ⟨c, u, v, hgdec⟩
  refine ⟨c, u, v, ?_⟩
  calc
    x = data.sigma g := hg.symm
    _ = data.sigma ((SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        primeLineElement p q c * SemidirectProduct.inr v) := by
      rw [hgdec]
    _ = data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q c) *
          data.sigma (SemidirectProduct.inr v : NormSet.normOneFrobeniusGroup p q) := by
      simp [map_mul]

/-- BG Appendix C, Lemma C.3 Step 2 inside concrete `P⋊U`: if
`s₁ u s₂` lies in the complement, then either both prime-line factors are
trivial or the complement factor is trivial and the prime-line factors cancel. -/
theorem generatorRelation_step2_primeLine (data : FieldNormalizerData p q G) {c d : ZMod p}
    (u : NormSet.normOneUnits p q)
    (hmem : (primeLineElement p q c *
        (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          primeLineElement p q d) ∈ NormSet.normOneFrobeniusComplement p q) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  have hmem_original :
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd
            ((algebraMap (ZMod p) (GaloisField p q) c) *
              (1 : GaloisField p q))) : NormSet.normOneFrobeniusGroup p q) *
        SemidirectProduct.inr u *
          SemidirectProduct.inl
            (Multiplicative.ofAdd
              ((algebraMap (ZMod p) (GaloisField p q) d) *
                (1 : GaloisField p q)))) ∈
        (SemidirectProduct.inr : NormSet.normOneUnits p q →*
          NormSet.normOneFrobeniusGroup p q).range := by
    simpa [primeLineElement, NormSet.normOneFrobeniusComplement,
      NormSet.normOneFrobeniusComplement] using hmem
  exact
    NormSet.normOneFrobenius_generatorRelation_step2_primeLine
      (p := p) (q := q) data.q_prime data.cyclotomic_coprime
      (s := (1 : GaloisField p q)) one_ne_zero
      (c := c) (d := d) u hmem_original

/-- BG Appendix C, Lemma C.3 Step 2 transported to `G`: the same alternative can
be read from membership of the transported product in `U`. -/
theorem generatorRelation_step2_primeLine_of_sigma_mem_U
    (data : FieldNormalizerData p q G)
    {c d : ZMod p} (u : NormSet.normOneUnits p q)
    (hmem : data.sigma (primeLineElement p q c) *
        data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q d) ∈ data.U) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  have hmem_map : data.sigma (primeLineElement p q c) *
        data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q d) ∈
      (NormSet.normOneFrobeniusComplement p q).map data.sigma := by
    rwa [data.sigma_U_eq_U]
  rcases hmem_map with ⟨g, hgU, hg⟩
  let prodH : NormSet.normOneFrobeniusGroup p q :=
    primeLineElement p q c *
      (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
        primeLineElement p q d
  have hprod_sigma : data.sigma prodH =
      data.sigma (primeLineElement p q c) *
        data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
          data.sigma (primeLineElement p q d) := by
    simp [prodH, map_mul]
  have hg_eq : g = prodH := data.sigma_injective (by
    rw [hg, hprod_sigma])
  have hmemH : prodH ∈ NormSet.normOneFrobeniusComplement p q := by
    simpa [← hg_eq] using hgU
  exact data.generatorRelation_step2_primeLine u hmemH

/-- The chosen nonidentity element `s ∈ P₀` cannot normalize `U`.  Otherwise a
nontrivial norm-one unit `u` would give `s u s⁻¹ ∈ U`, and BG Appendix C,
Lemma C.3 Step 2 forces `u = 1`. -/
theorem s_not_normalizes_U (data : FieldNormalizerData p q G) :
    data.s ∉ Subgroup.normalizer (data.U : Set G) := by
  intro hsN
  rcases exists_normOneUnit_ne_one p q data.q_prime.one_lt with ⟨u, hu_ne⟩
  have huU :
      data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) ∈
        data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  have hconjU :
      data.s *
          data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
            data.s⁻¹ ∈ data.U :=
    (Subgroup.mem_normalizer_iff.mp hsN
      (data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q))).mp huU
  have hsigma_inv :
      data.sigma (primeLineElement p q (-1)) = data.s⁻¹ := by
    rw [primeLineElement_neg p q (1 : ZMod p)]
    simp [s, primeLineElement_one]
  have hmem_step :
      data.sigma (primeLineElement p q 1) *
          data.sigma (SemidirectProduct.inr u : NormSet.normOneFrobeniusGroup p q) *
            data.sigma (primeLineElement p q (-1)) ∈ data.U := by
    simpa [s, primeLineElement_one, hsigma_inv] using hconjU
  have hstep :=
    data.generatorRelation_step2_primeLine_of_sigma_mem_U
      (c := (1 : ZMod p)) (d := (-1 : ZMod p)) u hmem_step
  rcases hstep with hzero | hone
  · have h1_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    exact h1_ne_zero hzero.1
  · exact hu_ne hone.1

end FieldNormalizerData

end OddOrder.BG.AppC
