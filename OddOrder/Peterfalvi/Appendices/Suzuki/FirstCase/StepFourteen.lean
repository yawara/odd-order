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

open scoped Pointwise commutatorElement

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

/-- If `N ≤ K` is normalized by `K` and `[K : N] = p²`, then `⁅K, K⁆ ≤ N`
(groups of order `p²` are commutative). -/
theorem commutator_le_of_card_eq_prime_sq_mul {K N : Subgroup G'} {p : ℕ}
    (hp : p.Prime) (hNK : N ≤ K)
    (hnorm : ∀ x ∈ K, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hcard : Nat.card ↥K = p ^ 2 * Nat.card ↥N) :
    ⁅K, K⁆ ≤ N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Ns : Subgroup ↥K := N.subgroupOf K with hNs_def
  haveI hNsn : Ns.Normal := by
    constructor
    intro n hn g
    rw [hNs_def, Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm (g : G') g.2 (n : G') hn
  have hNscard : Nat.card ↥Ns = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hidx : Nat.card (↥K ⧸ Ns) = p ^ 2 := by
    have h1 := Ns.card_mul_index
    rw [hNscard, hcard, Subgroup.index_eq_card] at h1
    have hpos : 0 < Nat.card ↥N := Nat.card_pos
    have h2 : Nat.card ↥N * Nat.card (↥K ⧸ Ns) = Nat.card ↥N * p ^ 2 := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  haveI : IsMulCommutative (↥K ⧸ Ns) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hidx
  have hcomm : _root_.commutator ↥K ≤ Ns :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hmap := Subgroup.map_mono (f := K.subtype) hcomm
  rw [Subgroup.map_subtype_commutator, hNs_def,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNK] at hmap
  exact hmap

/-- **At most `p + 1` subgroups of order `p` in a group of order `p²`**: distinct
ones meet trivially, so their `p - 1` nonidentity elements are disjoint inside the
`p² - 1` nonidentity elements of `E`. -/
theorem finset_card_prime_subgroups_le {E : Subgroup G'} {p : ℕ} (hp : p.Prime)
    (hE : Nat.card ↥E = p ^ 2) (𝒮 : Finset (Subgroup G'))
    (hmem : ∀ A ∈ 𝒮, A ≤ E ∧ Nat.card ↥A = p) :
    𝒮.card ≤ p + 1 := by
  classical
  haveI := Fintype.ofFinite G'
  have hpairinf : ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A ≠ B → A ⊓ B = ⊥ := by
    intro A hA B hB hne
    obtain ⟨-, hAc⟩ := hmem A hA
    obtain ⟨-, hBc⟩ := hmem B hB
    have hdvd : Nat.card ↥(A ⊓ B) ∣ p := by
      have h1 := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ B ≤ A)
      rwa [hAc] at h1
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have h2 : A ⊓ B = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp', hAc])
      have h3 : A ⊓ B = B :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hp', hBc])
      exact hne (h2.symm.trans h3)
  set D : Subgroup G' → Finset G' :=
    fun A => (A : Set G').toFinset \ {1} with hD_def
  have hDcard : ∀ A ∈ 𝒮, (D A).card = p - 1 := by
    intro A hA
    obtain ⟨-, hAc⟩ := hmem A hA
    have h1 : ({1} : Finset G') ⊆ (A : Set G').toFinset := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [Set.mem_toFinset, hx]
      exact A.one_mem
    rw [hD_def, Finset.card_sdiff, Finset.inter_eq_left.mpr h1,
      Finset.card_singleton]
    congr 1
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hAc
  have hdisj : ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A ≠ B → Disjoint (D A) (D B) := by
    intro A hA B hB hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hD_def] at hx hx'
    simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe,
      Finset.mem_singleton] at hx hx'
    have h1 : x ∈ A ⊓ B := ⟨hx.1, hx'.1⟩
    rw [hpairinf A hA B hB hne, Subgroup.mem_bot] at h1
    exact hx.2 h1
  have hsub : 𝒮.biUnion D ⊆ (E : Set G').toFinset \ {1} := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨A, hA, hxA⟩ := hx
    obtain ⟨hAE, -⟩ := hmem A hA
    rw [hD_def] at hxA
    simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe,
      Finset.mem_singleton] at hxA ⊢
    exact ⟨hAE hxA.1, hxA.2⟩
  have hEcard : ((E : Set G').toFinset \ {1}).card = p ^ 2 - 1 := by
    have h1 : ({1} : Finset G') ⊆ (E : Set G').toFinset := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [Set.mem_toFinset, hx]
      exact E.one_mem
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h1, Finset.card_singleton]
    congr 1
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hE
  have hsum : (𝒮.biUnion D).card = 𝒮.card * (p - 1) := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hDcard, Finset.sum_const,
      smul_eq_mul]
  have hle := Finset.card_le_card hsub
  rw [hsum, hEcard] at hle
  have h1lt := hp.one_lt
  have hpos : 0 < p - 1 := by omega
  have heq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    zify [h2, h1lt.le]
    ring
  rw [heq] at hle
  exact Nat.le_of_mul_le_mul_right hle hpos

/-- **Completeness of a `p + 1`-element list of order-`p` subgroups**: if `𝒮`
already lists `p + 1` distinct subgroups of order `p` of a group of order `p²`,
then every order-`p` subgroup occurs in `𝒮` (one more would exceed the bound). -/
theorem mem_of_card_eq_of_prime_subgroups {E : Subgroup G'} {p : ℕ} (hp : p.Prime)
    (hE : Nat.card ↥E = p ^ 2) (𝒮 : Finset (Subgroup G'))
    (hmem : ∀ A ∈ 𝒮, A ≤ E ∧ Nat.card ↥A = p) (hcard : 𝒮.card = p + 1)
    {A : Subgroup G'} (hAE : A ≤ E) (hAc : Nat.card ↥A = p) : A ∈ 𝒮 := by
  classical
  by_contra hA
  have h1 : (insert A 𝒮).card = p + 2 := by
    rw [Finset.card_insert_of_notMem hA, hcard]
  have h2 := finset_card_prime_subgroups_le hp hE (insert A 𝒮) (fun B hB => by
    rcases Finset.mem_insert.mp hB with rfl | hB'
    · exact ⟨hAE, hAc⟩
    · exact hmem B hB')
  omega

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

include model in
/-- **Peterfalvi Part II, Ch. II, step (14): `⁅RΣ, RΣ⁆ = Z₁`** (p. 113).

Both `Z₁P` and `T` have index `9 = 3²` in `RΣ` and are normalized by it (the
first is central by (14)(i), the second because `R` is abelian and `Σ`
normalizes `T`), so the commutator subgroup lies in `Z₁P ⊓ T = Z₁` (Dedekind,
using `Z₁ ≤ T` and `T ⊓ P = 1`).  It is nontrivial since `RΣ` is nonabelian,
and `|Z₁| = 3` is prime. -/
theorem commutator_sup_eq_zpowers
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) :
    ⁅fc.invImageF model
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)),
        fc.invImageF model
          ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G))⁆
      = Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
          * fc.toHypothesis.t) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨hpSig, hp3, hF9, -, -, -⟩ := fc.step_twelve model ind hB2
  obtain ⟨-, -, -, hSig3, -⟩ :=
    fc.card_field_eq_nine_of_p_dvd_card_centralizer_W ind model hB2 hpSig
  have hm : Nat.card F = fc.p ^ 2 := by rw [hF9, hp3]; norm_num
  set R : Subgroup G := fc.invImageF model with hR_def
  set Sg : Subgroup G :=
    fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G) with hSg_def
  set T : Subgroup G := fc.sInvertedT model with hT_def
  set Z₁ : Subgroup G := Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
    * fc.toHypothesis.t) with hZ₁_def
  have hPcard : Nat.card ↥fc.P = 3 := by rw [fc.card_P, hp3]
  have hRcard : Nat.card ↥R = 27 := by
    rw [hR_def, fc.card_invImageF model ind, hF9, hPcard]
  have hRScard : Nat.card ↥(R ⊔ Sg) = 81 := by
    rw [hR_def, hSg_def, fc.card_sup_invImageF_centralizer_W model ind]
    rw [← hR_def, ← hSg_def, hRcard, hSig3]
  have hTcard : Nat.card ↥T = 9 := by
    rw [hT_def, fc.card_sInvertedT model ind hB2 hm, hF9]
  have hstord : orderOf (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) = 3 := by
    rw [fc.orderOf_st_eq_char model, fc.char_eq_p model hB2, hp3]
  have hZ₁card : Nat.card ↥Z₁ = 3 := by rw [hZ₁_def, Nat.card_zpowers, hstord]
  have hZ₁T : Z₁ ≤ T :=
    fc.zpowers_distinguishedInvolution_mul_t_le_sInvertedT model ind hB2 hm
  have hTR : T ≤ R := (fc.sInvertedT_spec model ind hB2 hm).1
  have hPR : fc.P ≤ R := fc.P_le_invImageF model
  have habR := fc.invImageF_mul_comm model ind hB2 hm
  -- `⁅RΣ, RΣ⁆ ≤ Z₁P` (the quotient by the central `Z₁P` has order 9)
  have hZ₁Pcard : Nat.card ↥(Z₁ ⊔ fc.P) = 9 := by
    have hZ₁P : Z₁ ⊓ fc.P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ T ⊓ fc.P := ⟨hZ₁T hx.1, hx.2⟩
      rwa [(fc.sInvertedT_spec model ind hB2 hm).2.2.2] at hx'
    rw [card_sup_eq_mul_of_commute
      (fun a ha b hb => habR a (hZ₁T ha |> hTR) b (hPR hb)) hZ₁P, hZ₁card, hPcard]
  have hcentral := fc.zpowers_mul_t_sup_P_le_center_sup model ind hB2 hm
  have hle1 : ⁅R ⊔ Sg, R ⊔ Sg⁆ ≤ Z₁ ⊔ fc.P := by
    refine commutator_le_of_card_eq_prime_sq_mul (p := 3) (by norm_num)
      (fun x hx => (hcentral hx).1) (fun x hx n hn => ?_)
      (by rw [hRScard, hZ₁Pcard]; norm_num)
    have hcomm : x * n = n * x :=
      Subgroup.mem_centralizer_iff.mp (hcentral hn).2 x hx
    have h1 : x * n * x⁻¹ = n := by rw [hcomm]; group
    rw [h1]
    exact hn
  -- `⁅RΣ, RΣ⁆ ≤ T` (the quotient by `T` has order 9 as well)
  have hTle : T ≤ R ⊔ Sg := hTR.trans le_sup_left
  have hle2 : ⁅R ⊔ Sg, R ⊔ Sg⁆ ≤ T := by
    refine commutator_le_of_card_eq_prime_sq_mul (p := 3) (by norm_num) hTle
      (fun x hx n hn => ?_) (by rw [hRScard, hTcard]; norm_num)
    -- `R` normalizes `T` (it is abelian) and so does `Σ`
    have hnormR : ∀ r ∈ R, ∀ y ∈ T, r * y * r⁻¹ ∈ T := by
      intro r hr y hy
      have h1 : r * y * r⁻¹ = y := by
        rw [habR r hr y (hTR hy)]; group
      rw [h1]; exact hy
    have hnormS : ∀ w ∈ Sg, ∀ y ∈ T, w * y * w⁻¹ ∈ T := by
      intro w hw y hy
      exact fc.conj_mem_sInvertedT_of_mem_centralizer_W model ind hB2 hm
        hw.1 hw.2 hy
    have hnormRS : ∀ z ∈ R ⊔ Sg, ∀ y ∈ T, z * y * z⁻¹ ∈ T := by
      intro z hz y hy
      have hz' : z ∈ ((R : Set G) * (Sg : Set G)) := by
        rw [← fc.coe_sup_invImageF_centralizer_W model]
        exact hz
      obtain ⟨r, hr, w, hw, rfl⟩ := hz'
      have h2 : r * w * y * (r * w)⁻¹ = r * (w * y * w⁻¹) * r⁻¹ := by group
      rw [h2]
      exact hnormR r hr _ (hnormS w hw y hy)
    exact hnormRS x hx n hn
  -- `Z₁P ⊓ T = Z₁` and the commutator is nontrivial
  have hinf : (Z₁ ⊔ fc.P) ⊓ T = Z₁ := by
    refine le_antisymm ?_ (le_inf le_sup_left hZ₁T)
    intro x hx
    obtain ⟨hxZP, hxT⟩ := hx
    have hxZP' : x ∈ ((Z₁ : Set G) * (fc.P : Set G)) := by
      have hcoe : ((Z₁ ⊔ fc.P : Subgroup G) : Set G)
          = (Z₁ : Set G) * (fc.P : Set G) := by
        refine Subgroup.coe_mul_of_right_le_normalizer_left _ _ ?_
        intro b hb
        rw [Subgroup.mem_normalizer_iff]
        intro a
        constructor
        · intro ha
          have h1 : b * a * b⁻¹ = a := by
            rw [← habR a (hTR (hZ₁T ha)) b (hPR hb)]; group
          rw [h1]; exact ha
        · intro ha
          have h1 : (b * a * b⁻¹) * b = b * (b * a * b⁻¹) :=
            habR _ (hTR (hZ₁T ha)) b (hPR hb)
          have h2 : b * a = b * (b * a * b⁻¹) := by rw [← h1]; group
          have h3 : a = b * a * b⁻¹ := mul_left_cancel h2
          rw [h3]; exact ha
      rw [← hcoe]; exact hxZP
    obtain ⟨z, hz, y, hy, rfl⟩ := hxZP'
    -- `y = z⁻¹·(zy) ∈ P ⊓ T = 1`
    have hyT : y ∈ T := by
      have h4 : y = z⁻¹ * (z * y) := by group
      rw [h4]
      exact mul_mem (T.inv_mem (hZ₁T hz)) hxT
    have hyb : y ∈ T ⊓ fc.P := ⟨hyT, hy⟩
    rw [(fc.sInvertedT_spec model ind hB2 hm).2.2.2, Subgroup.mem_bot] at hyb
    simpa [hyb] using hz
  have hne : ⁅R ⊔ Sg, R ⊔ Sg⁆ ≠ ⊥ := by
    intro h
    have hnc : ∀ x ∈ R ⊔ Sg, ∀ y ∈ R ⊔ Sg, x * y = y * x := by
      intro x hx y hy
      have hmem : ⁅x, y⁆ ∈ ⁅R ⊔ Sg, R ⊔ Sg⁆ := Subgroup.commutator_mem_commutator hx hy
      rw [h, Subgroup.mem_bot] at hmem
      exact (commutatorElement_eq_one_iff_mul_comm.mp hmem)
    -- but a nonidentity element of `Σ` does not centralize `R`
    have hSgne : Sg ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hSig3
      omega
    obtain ⟨w, hwSg, hw1⟩ : ∃ w ∈ Sg, w ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hSgne (by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        exact hcon x hx)
    refine fc.not_forall_comm_of_mem_centralizer_W model ind hwSg.1 hwSg.2 hw1 ?_
    intro r hr
    exact hnc w ((le_sup_right : Sg ≤ R ⊔ Sg) hwSg) r
      ((le_sup_left : R ≤ R ⊔ Sg) hr)
  -- a nontrivial subgroup of the order-3 group `Z₁`
  have hcle : ⁅R ⊔ Sg, R ⊔ Sg⁆ ≤ Z₁ := by
    rw [← hinf]
    exact le_inf hle1 hle2
  refine Subgroup.eq_of_le_of_card_ge hcle ?_
  have hdvd := Subgroup.card_dvd_of_le hcle
  rw [hZ₁card] at hdvd
  rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
  · exfalso
    exact hne (Subgroup.card_eq_one.mp h1)
  · rw [h3, hZ₁card]

include model in
/-- **`N_G(RΣ)` normalizes `Z₁`** ((14), p. 113): `Z₁ = ⁅RΣ, RΣ⁆` is preserved by
every automorphism of `RΣ`, in particular by conjugation from `N_G(RΣ)`. -/
theorem conj_mem_zpowers_of_mem_normalizer_sup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {g : G}
    (hg : g ∈ Subgroup.normalizer
      (((fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
          : Subgroup G) : Set G)) {x : G}
    (hx : x ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t)) :
    g * x * g⁻¹ ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set K : Subgroup G := fc.invImageF model
    ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) with hK_def
  have hKn : ∀ y : G, y ∈ K ↔ g * y * g⁻¹ ∈ K :=
    Subgroup.mem_set_normalizer_iff.mp hg
  have hcomm := fc.commutator_sup_eq_zpowers model ind hB2
  rw [← hcomm] at hx ⊢
  have hmapK : K.map (MulAut.conj g).toMonoidHom = K := by
    ext y
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hKn z).mp hz
    · intro hy
      refine ⟨g⁻¹ * y * g, (hKn (g⁻¹ * y * g)).mpr ?_, ?_⟩
      · have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [h1]; exact hy
      · change g * (g⁻¹ * y * g) * g⁻¹ = y
        group
  have hmem : (MulAut.conj g).toMonoidHom x
      ∈ (⁅K, K⁆).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [Subgroup.map_commutator, hmapK] at hmem
  exact hmem

include model in
/-- **`N_G(RΣ)` normalizes `Z₁P`** ((14), p. 113): `Z₁P = Z(RΣ)` is preserved by
conjugation from `N_G(RΣ)` (an automorphism of `RΣ` preserves its centre). -/
theorem conj_mem_zpowers_sup_P_of_mem_normalizer_sup
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G)) {g : G}
    (hg : g ∈ Subgroup.normalizer
      (((fc.invImageF model
        ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)))
          : Subgroup G) : Set G)) {x : G}
    (hx : x ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
        * fc.toHypothesis.t) ⊔ fc.P) :
    g * x * g⁻¹ ∈ Subgroup.zpowers (fc.toHypothesis.distinguishedInvolution
      * fc.toHypothesis.t) ⊔ fc.P := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  set K : Subgroup G := fc.invImageF model
    ⊔ (fc.toHypothesis.W ⊓ Subgroup.centralizer (fc.P : Set G)) with hK_def
  have hKg : ∀ y : G, y ∈ K ↔ g * y * g⁻¹ ∈ K :=
    Subgroup.mem_set_normalizer_iff.mp hg
  have hcent := fc.inf_centralizer_sup_eq_zpowers_sup_P model ind hB2
  rw [← hcent] at hx ⊢
  refine Subgroup.mem_inf.mpr ⟨(hKg x).mp (Subgroup.mem_inf.mp hx).1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  -- `g⁻¹ y g ∈ K` commutes with `x`
  have hyK : g⁻¹ * y * g ∈ K := by
    refine (hKg (g⁻¹ * y * g)).mpr ?_
    have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [h1]
    exact hy
  have hcx : (g⁻¹ * y * g) * x = x * (g⁻¹ * y * g) :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 _ hyK
  calc y * (g * x * g⁻¹)
      = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcx]
    _ = (g * x * g⁻¹) * y := by group

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
