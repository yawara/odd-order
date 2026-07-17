import OddOrder.Peterfalvi.S15_SAndT_Setup.Machinery135

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT_Setup.DegreesFirstSplit` (2000-line limit, issue
0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


section GenericAlpha

/-! ### The (13.5.a) machinery over an abstract (7.6) datum

Generic forms of the point formula and the correction-term `α` cluster, over any
`H76 : Hypothesis76 G A L` whose `ρ` is the identity on `A` (the TI case) and any
"kernel" subgroup `P' ≤ L`.  Instantiated by the `S`-side (`H_sharp_*`, `P' = P.subgroupOf S`)
and the `T`-side ((13.8): `Q_sharp_hypothesis76`, `P' = Q.subgroupOf T`). -/

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.a) point formula, `a = 0` form: if every `P'`-non-kernel coefficient of `χ`
vanishes, then on `A` the character `χ` is its `P'`-kernel tail. -/
theorem hypothesis76_point_formula_kernel_only [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (hHbot : ∀ a : {a : G // a ∈ A}, H76.hyp71.hyp.H a = ⊥)
    (P' : Subgroup ↥L) (χ : ClassFunction G ℂ)
    (hall : ∀ i : Fin (H76.n + 1), 0 < i →
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) →
      H76.cCoeff χ i = 0)
    (a : ↥L) (ha : (a : G) ∈ A) :
    χ (a : G) =
      ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
            (fun i => (P' : Set ↥L) ⊆
              OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a := by
  classical
  have hbase : χ (a : G) = ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a :=
    (chiRho_eq_self_of_H_eq_bot H76.hyp71 hHbot χ a ha).symm.trans
      (OddOrder.Peterfalvi.S09.Hypothesis76.chiRho_explicit_formula H76 χ ha)
  rw [hbase, ← Finset.sum_filter_add_sum_filter_not (Finset.Ioi 0)
    (fun i => (P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))]
  have hmid0 : ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter (fun i =>
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter] at hi
    rw [hall i (Finset.mem_Ioi.mp hi.1) hi.2, star_zero, zero_div, zero_mul]
  rw [hmid0, add_zero]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.a) point formula with a distinguished index (`a ≠ 0` form): the `P'`-non-kernel
middle coefficients vanish, leaving the `i₁`-term plus the `P'`-kernel tail. -/
theorem hypothesis76_point_formula [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (hHbot : ∀ a : {a : G // a ∈ A}, H76.hyp71.hyp.H a = ⊥)
    (P' : Subgroup ↥L) (χ : ClassFunction G ℂ)
    (i₁ : Fin (H76.n + 1)) (hi₁ : 0 < i₁)
    (hi₁ker : ¬ ((P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i₁)))
    (hmiddle : ∀ i : Fin (H76.n + 1), 0 < i → i ≠ i₁ →
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) →
      H76.cCoeff χ i = 0)
    (a : ↥L) (ha : (a : G) ∈ A) :
    χ (a : G) =
      (star (H76.cCoeff χ i₁) / H76.zetaNormSq i₁) * H76.zeta i₁ a
      + ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
            (fun i => (P' : Set ↥L) ⊆
              OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a := by
  classical
  have hbase : χ (a : G) = ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a :=
    (chiRho_eq_self_of_H_eq_bot H76.hyp71 hHbot χ a ha).symm.trans
      (OddOrder.Peterfalvi.S09.Hypothesis76.chiRho_explicit_formula H76 χ ha)
  rw [hbase, ← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr hi₁)]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Ioi 0).erase i₁)
      (fun i => (P' : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))]
  have hmid0 : ∑ i ∈ ((Finset.Ioi 0).erase i₁).filter (fun i =>
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_erase] at hi
    rw [hmiddle i (Finset.mem_Ioi.mp hi.1.2) hi.1.1 hi.2, star_zero, zero_div, zero_mul]
  have hi₁notin : i₁ ∉ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
      (fun i => (P' : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) := by
    rw [Finset.mem_filter]
    exact fun h => hi₁ker h.2
  rw [hmid0, add_zero, Finset.filter_erase, Finset.erase_eq_self.mpr hi₁notin]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.a) correction term: the `P'`-kernel tail of the (7.7.a) decomposition. -/
noncomputable def hypothesis76AlphaFun [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) : ↥L → ℂ :=
  fun a =>
    ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
          (fun i => (P' : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
        (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The generic (13.5.a) correction as a class function on `↥L`.  This is the
class-function realization of `hypothesis76AlphaFun`, needed when restricting the correction
to the normal subgroup `H76.H.subgroupOf L`. -/
noncomputable def hypothesis76AlphaCF [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) : ClassFunction ↥L ℂ :=
  ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
        (fun i => (P' : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) • H76.zeta i

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
@[simp] theorem hypothesis76AlphaCF_apply [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) (a : ↥L) :
    hypothesis76AlphaCF H76 P' χ a = hypothesis76AlphaFun H76 P' χ a := by
  rw [hypothesis76AlphaCF, hypothesis76AlphaFun,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [ClassFunction.smul_apply])

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The generic correction is constant on `P'`. -/
theorem hypothesis76AlphaFun_const [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) :
    ∀ x ∈ P', hypothesis76AlphaFun H76 P' χ x = hypothesis76AlphaFun H76 P' χ 1 := by
  classical
  intro x hx
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hker := (Finset.mem_filter.mp hi).2
  rw [show H76.zeta i x = H76.zeta i 1 from hker hx]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The generic correction vanishes off `H76.H`. -/
theorem hypothesis76AlphaFun_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) :
    ∀ x : ↥L, (x : G) ∉ H76.H → hypothesis76AlphaFun H76 P' χ x = 0 := by
  classical
  intro x hx
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [H76.zeta_eq_zero_of_not_mem_H i x hx, mul_zero]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.c): the inflation bound for the correction over any sharp `Finset` of the
`H76.H`-members (instance-free `F`-interface). -/
theorem hypothesis76AlphaFun_inflation [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ)
    (F : Finset ↥L) (hF : ∀ x : ↥L, x ∈ F ↔ ((x : G) ∈ H76.H ∧ x ≠ 1))
    (_hP'H : ∀ x : ↥L, x ∈ P' → (x : G) ∈ H76.H) :
    ((Nat.card ↥P' : ℝ) - 1) * ‖hypothesis76AlphaFun H76 P' χ 1‖ ^ 2
      ≤ ∑ x ∈ F, ‖hypothesis76AlphaFun H76 P' χ x‖ ^ 2 := by
  classical
  set α := hypothesis76AlphaFun H76 P' χ with hαdef
  have hcore := sum_normSq_erase_one_ge_of_const_on_subgroup P' α
    (hypothesis76AlphaFun_const H76 P' χ)
  -- The ambient `↥L`-sum equals the `F`-sum plus the identity term (α vanishes off `H76.H`).
  have hFeq : F = (Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  have hsupp : ∑ x : ↥L, ‖α x‖ ^ 2
      = ∑ x ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H), ‖α x‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : ↥L => (x : G) ∈ H76.H)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x : ↥L => ¬ (x : G) ∈ H76.H), ‖α x‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hαdef, hypothesis76AlphaFun_eq_zero H76 P' χ x (Finset.mem_filter.mp hx).2]
      simp
    rw [h0, add_zero]
  have h1mem : (1 : ↥L) ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [OneMemClass.coe_one]
    exact H76.H.one_mem
  have hsharp : ∑ x ∈ F, ‖α x‖ ^ 2
      = (∑ x ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H), ‖α x‖ ^ 2)
        - ‖α 1‖ ^ 2 := by
    rw [hFeq, ← Finset.add_sum_erase _ _ h1mem]
    ring
  rw [hsharp, ← hsupp]
  exact hcore

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- For an abstract (7.6) datum, restriction of a family member to its inducing normal
subgroup is its squared norm times the orbit sum of an inducing irreducible character. -/
theorem hypothesis76_restrict_zeta_eq_orbitSum [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (j : Fin (H76.n + 1)) :
    ∃ θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(H76.H.subgroupOf L),
      H76.zeta j = ClassFunction.induce (H76.H.subgroupOf L)
          (θ : ClassFunction ↥(H76.H.subgroupOf L) ℂ) ∧
      (haveI : (H76.H.subgroupOf L).Normal :=
        OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
      ClassFunction.restrict (H76.H.subgroupOf L) (H76.zeta j)
        = H76.zetaNormSq j •
            ∑ ψ ∈ Finset.univ.image (fun x : ↥L =>
              ClassFunction.conjBy x⁻¹
                (θ : ClassFunction ↥(H76.H.subgroupOf L) ℂ)), ψ) := by
  classical
  set K : Subgroup ↥L := H76.H.subgroupOf L with hKdef
  haveI hKnorm : K.Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
  obtain ⟨θ₀, hθ₀⟩ := H76.zeta_induced j
  have hθ : H76.zeta j = ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) := by
    rw [hθ₀]
  refine ⟨θ₀, hθ, ?_⟩
  have hK0 : (Nat.card ↥K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have horbit := OddOrder.RepresentationTheory.card_smul_restrict_induce_eq_inertia_smul_orbitSum
    (G := ↥L) (H := K) (k := ℂ) (θ₀ : ClassFunction ↥K ℂ)
  have hinertia := OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
    (G := ↥L) (H := K) θ₀
  have hnormval : (Nat.card ↥K : ℂ) * H76.zetaNormSq j
      = (Nat.card ↥(ClassFunction.inertia (G := ↥L)
          (θ₀ : ClassFunction ↥K ℂ)) : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hθ]
    exact hinertia
  have hIKnorm : ((Nat.card ↥K : ℂ))⁻¹ *
      (Nat.card ↥(ClassFunction.inertia (G := ↥L)
        (θ₀ : ClassFunction ↥K ℂ)) : ℂ) = H76.zetaNormSq j := by
    rw [← hnormval]
    field_simp
  have h1 : (Nat.card ↥K : ℂ) • ClassFunction.restrict K (H76.zeta j)
      = ((Nat.card ↥(ClassFunction.inertia (G := ↥L)
          (θ₀ : ClassFunction ↥K ℂ)) : ℕ) : ℂ) •
          ∑ ψ ∈ Finset.univ.image
            (fun x : ↥L => ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ)] at horbit
    rw [hθ]
    exact horbit
  have h2 := congrArg (fun φ => ((Nat.card ↥K : ℂ))⁻¹ • φ) h1
  simp only [smul_smul, inv_mul_cancel₀ hK0, one_smul] at h2
  rw [h2, hIKnorm]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The normalized restriction `Res ζ_i / ‖ζ_i‖²` of an abstract (7.6) family member is a
virtual character: it is the orbit sum of the inducing irreducible character. -/
theorem hypothesis76_inv_normSq_restrict_zeta_mem_ZIrr [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (i : Fin (H76.n + 1)) :
    (H76.zetaNormSq i)⁻¹ •
        ClassFunction.restrict (H76.H.subgroupOf L) (H76.zeta i)
      ∈ ZIrr ↥(H76.H.subgroupOf L) := by
  classical
  set K : Subgroup ↥L := H76.H.subgroupOf L with hKdef
  haveI hKnorm : K.Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
  obtain ⟨θ₀, hθ₀⟩ := H76.zeta_induced i
  have hθ : H76.zeta i = ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) := by
    rw [hθ₀]
  have hinertia := OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
    (G := ↥L) (H := K) θ₀
  have hnormval : (Nat.card ↥K : ℂ) * H76.zetaNormSq i
      = (Nat.card ↥(ClassFunction.inertia (G := ↥L)
          (θ₀ : ClassFunction ↥K ℂ)) : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hθ]
    exact hinertia
  have hI0 : (Nat.card ↥(ClassFunction.inertia (G := ↥L)
      (θ₀ : ClassFunction ↥K ℂ)) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hnorm0 : H76.zetaNormSq i ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnormval
    exact hI0 hnormval.symm
  obtain ⟨θ, -, hres⟩ := hypothesis76_restrict_zeta_eq_orbitSum H76 i
  have hmain : (H76.zetaNormSq i)⁻¹ •
      ClassFunction.restrict K (H76.zeta i)
      = ∑ ψ ∈ Finset.univ.image (fun x : ↥L =>
          ClassFunction.conjBy x⁻¹ (θ : ClassFunction ↥K ℂ)), ψ := by
    rw [hres, smul_smul, inv_mul_cancel₀ hnorm0, one_smul]
  rw [hmain]
  exact OddOrder.RepresentationTheory.orbitSum_mem_ZIrr (G := ↥L) θ

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- If the (7.7.a) coefficients are integral, the generic `P'`-kernel correction restricts
to a virtual character of `H76.H`. -/
theorem hypothesis76AlphaCF_restrict_mem_ZIrr [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ)
    (hc : ∀ i, ∃ z : ℤ, H76.cCoeff χ i = (z : ℂ)) :
    ClassFunction.restrict (H76.H.subgroupOf L) (hypothesis76AlphaCF H76 P' χ)
      ∈ ZIrr ↥(H76.H.subgroupOf L) := by
  classical
  set K : Subgroup ↥L := H76.H.subgroupOf L with hKdef
  have hlin : ClassFunction.restrict K (hypothesis76AlphaCF H76 P' χ)
      = ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
            (fun i => (P' : Set ↥L) ⊆
              OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) •
            ClassFunction.restrict K (H76.zeta i) := by
    ext x
    rw [ClassFunction.restrict_apply, hypothesis76AlphaCF,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [ClassFunction.smul_apply, ClassFunction.smul_apply, ClassFunction.restrict_apply])
  rw [hlin]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  obtain ⟨z, hz⟩ := hc i
  rw [hz, star_intCast, div_eq_mul_inv, mul_smul, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ z (hypothesis76_inv_normSq_restrict_zeta_mem_ZIrr H76 i)

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Generic (13.5.a) `P'`-kernel orthogonality**: the full-`↥L` pairing of a `P'`-non-kernel
family member `ζ_{i₁}` against the `P'`-kernel tail `α` vanishes — each tail constituent is a
family member of a *different* fibre (the kernel property separates them), and distinct-fibre
induced characters are orthogonal (`inner_induce_eq_zero_of_not_conj` via `zeta_induced`). -/
theorem hypothesis76_zeta_inner_alphaFun_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) (i₁ : Fin (H76.n + 1))
    (hi₁ker : ¬ ((P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i₁))) :
    ∑ x : ↥L, H76.zeta i₁ x * (starRingEnd ℂ) (hypothesis76AlphaFun H76 P' χ x) = 0 := by
  classical
  haveI hKn : (H76.H.subgroupOf L).Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
  -- The sum is `|L|·⟨ζ_{i₁}, alphaCF⟩` with `alphaCF` the class-function form of the tail.
  set alphaCF : ClassFunction ↥L ℂ :=
    ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
          (fun i => (P' : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
        (star (H76.cCoeff χ i) / H76.zetaNormSq i) • H76.zeta i with halphaCF
  have happly : ∀ x : ↥L, alphaCF x = hypothesis76AlphaFun H76 P' χ x := by
    intro x
    rw [halphaCF, OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply,
      hypothesis76AlphaFun]
    exact Finset.sum_congr rfl (fun i _ => by rw [ClassFunction.smul_apply])
  have hsum : ∑ x : ↥L, H76.zeta i₁ x * (starRingEnd ℂ)
      (hypothesis76AlphaFun H76 P' χ x)
      = ClassFunction.innerSum (H76.zeta i₁) alphaCF := by
    rw [ClassFunction.innerSum]
    exact Finset.sum_congr rfl (fun x _ => by rw [happly, starRingEnd_apply])
  rw [hsum, ← ClassFunction.card_mul_inner]
  have hinner0 : ClassFunction.inner (H76.zeta i₁) alphaCF = 0 := by
    rw [halphaCF, inner_sum_right]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [OddOrder.RepresentationTheory.inner_smul_right]
    have hjker := (Finset.mem_filter.mp hj).2
    have hzne : H76.zeta i₁ ≠ H76.zeta j := fun heq => hi₁ker (heq ▸ hjker)
    obtain ⟨θ, hθ⟩ := H76.zeta_induced i₁
    obtain ⟨θ', hθ'⟩ := H76.zeta_induced j
    have hz0 : ClassFunction.inner (H76.zeta i₁) (H76.zeta j) = 0 := by
      rw [hθ, hθ']
      refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ θ'
        (fun g hconj => ?_)
      refine hzne ?_
      rw [hθ, hθ', ← hconj, OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy,
        OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq]
    rw [hz0, mul_zero]
  rw [hinner0, mul_zero]

end GenericAlpha

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Peterfalvi (13.5.a), base decomposition**: on `H^#`, `χ` equals the (7.7.a) `ρ`-decomposition
`∑_{i≥1} (c̄_i / ‖ζ_i‖²) ζ_i` of the coherent datum `H_sharp_hypothesis76`.  Combines the `χ = χ^ρ`
bridge `chiRho_eq_self_of_H_eq_bot` (TI case, `H(a) = ⊥`) with `chiRho_explicit_formula` (7.7.a).
The
full (13.5.a) point formula `χ = (a/‖ζ₁‖²)ζ₁ + α` (with `P` off the kernels of `α`) then follows by
extracting the distinguished `ζ₁` term and grouping the `P`-kernel tail of this sum. -/
theorem H_sharp_chiRho_eq_explicit [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) (a : hyp.S)
    (ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) :
    χ (a : G) = ∑ i ∈ Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1)),
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
          (H_sharp_hypothesis76 hG hyp).zetaNormSq i) *
        (H_sharp_hypothesis76 hG hyp).zeta i a :=
  (chiRho_eq_self_of_H_eq_bot (H_sharp_hypothesis71 hG hyp) (fun _ => rfl) χ a ha).symm.trans
    (OddOrder.Peterfalvi.S09.Hypothesis76.chiRho_explicit_formula (H_sharp_hypothesis76 hG hyp) χ
        ha)

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Peterfalvi (13.5.a), point formula**: on `H^#`, the test character `χ` decomposes as the
distinguished term `(c̄_{i₁}/‖ζ_{i₁}‖²) ζ_{i₁}` plus the **`P`-kernel tail**
`α = ∑_{P⊆ker ζ_i, i≥1}`.
From the base decomposition `H_sharp_chiRho_eq_explicit` (χ = ∑_{i≥1} of the `ρ`-coefficients) one
extracts the distinguished index `i₁` (which is `P`-non-kernel, `hi1_ker`) and drops the `S₁`-middle
indices (`P`-non-kernel, `≠ i₁`) whose coefficients vanish by the (13.5) orthogonality hypothesis
`hmiddle` (`χ ⊥ (ζ_i − ζ_0)^τ`); what remains is the distinguished term and the `P⊆ker` tail.  The
tail `α` is constant on `P` (each `ζ_i` has `P` in its kernel), feeding (13.5.c). -/
theorem H_sharp_point_formula [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (χ : ClassFunction G ℂ)
    (i1 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1)) (hi1 : 0 < i1)
    (hi1_ker : ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i1)))
    (hmiddle : ∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i → i ≠ i1 →
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) →
      (H_sharp_hypothesis76 hG hyp).cCoeff χ i = 0)
    (a : hyp.S) (ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) :
    χ (a : G) =
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i1) /
          (H_sharp_hypothesis76 hG hyp).zetaNormSq i1) * (H_sharp_hypothesis76 hG hyp).zeta i1 a
      + ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
            (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
              OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
          (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
            (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a :=
                by
  classical
  rw [H_sharp_chiRho_eq_explicit hG hyp χ a ha,
    ← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr hi1)]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Ioi 0).erase i1)
      (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i))]
  have hmid0 : ∑ i ∈ ((Finset.Ioi 0).erase i1).filter (fun i =>
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i))),
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
        (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a = 0 :=
            by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_erase] at hi
    rw [hmiddle i (Finset.mem_Ioi.mp hi.1.2) hi.1.1 hi.2, star_zero, zero_div, zero_mul]
  have hi1notin : i1 ∉ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
      (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) := by
    rw [Finset.mem_filter]; exact fun h => hi1_ker h.2
  rw [hmid0, add_zero, Finset.filter_erase, Finset.erase_eq_self.mpr hi1notin]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Peterfalvi (13.5.a), point formula for `a = 0`**: if *every* `P`-non-kernel coefficient of
`χ` vanishes (the (13.5) hypothesis with `a = 0`, as for `χ = η₁₀` which is orthogonal to all of
`S^{τ₁}`), then on `H^#` the character `χ` *is* its `P`-kernel tail.  The `i₁`-free variant of
`H_sharp_point_formula`. -/
theorem H_sharp_point_formula_kernel_only [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (χ : ClassFunction G ℂ)
    (hall : ∀ i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1), 0 < i →
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)) →
      (H_sharp_hypothesis76 hG hyp).cCoeff χ i = 0)
    (a : hyp.S) (ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) :
    χ (a : G) =
      ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
            (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
              OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
          (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
            (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a :=
                by
  classical
  rw [H_sharp_chiRho_eq_explicit hG hyp χ a ha,
    ← Finset.sum_filter_add_sum_filter_not (Finset.Ioi 0)
      (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i))]
  have hmid0 : ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter (fun i =>
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i))),
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
        (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a = 0 :=
            by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter] at hi
    rw [hall i (Finset.mem_Ioi.mp hi.1) hi.2, star_zero, zero_div, zero_mul]
  rw [hmid0, add_zero]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.5.a) correction term `α`** for a test character `χ`: the `P`-kernel tail
`α = ∑_{i≥1, P⊆ker ζ_i} (c̄_i/‖ζ_i‖²)·ζ_i` of the (7.7.a) decomposition, as a function on `↥S`.
By `H_sharp_point_formula` (resp. the `a = 0` variant), `χ = (distinguished term) + α` (resp.
`χ = α`) on `H^#`; it is constant on `P` (`H_sharp_alphaFun_const_on_P`) and vanishes off `H`
(`H_sharp_alphaFun_eq_zero_of_not_mem`), which drive the (13.5.c) inflation bound. -/
noncomputable def H_sharp_alphaFun [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) : ↥hyp.S → ℂ :=
  fun a =>
    ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
          (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
            OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
        (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
          (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (13.5.a) correction `α` is **constant on `P`** — each `ζ_i` in the tail has `P` in its
kernel (`ζ_i(x) = ζ_i(1)` for `x ∈ P`), so the tail is `P`-constant.  The kernel input to
(13.5.c). -/
theorem H_sharp_alphaFun_const_on_P [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) :
    ∀ x ∈ hyp.P.subgroupOf hyp.S, H_sharp_alphaFun hG hyp χ x = H_sharp_alphaFun hG hyp χ 1 := by
  classical
  intro x hx
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hker := (Finset.mem_filter.mp hi).2
  have hx1 : (H_sharp_hypothesis76 hG hyp).zeta i x
      = (H_sharp_hypothesis76 hG hyp).zeta i 1 := hker hx
  rw [hx1]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (13.5.a) correction `α` **vanishes off `H`** — each induced `ζ_i` does
(`zeta_eq_zero_of_not_mem_H`). -/
theorem H_sharp_alphaFun_eq_zero_of_not_mem [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) :
    ∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → H_sharp_alphaFun hG hyp χ x = 0 := by
  classical
  intro x hx
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have h0 : (H_sharp_hypothesis76 hG hyp).zeta i x = 0 := by
    refine (H_sharp_hypothesis76 hG hyp).zeta_eq_zero_of_not_mem_H i x ?_
    intro hmem
    exact hx (Subgroup.mem_subgroupOf.mpr (by
      rwa [show (H_sharp_hypothesis76 hG hyp).H = hyp.H from rfl] at hmem))
  rw [h0, mul_zero]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Peterfalvi (13.5.c) for the concrete correction `α`**: the inflation bound
`(|P|−1)·‖α(1)‖² ≤ ∑_{x∈H^#}‖α(x)‖²` — `α` is `P`-constant (`H_sharp_alphaFun_const_on_P`), so
the `P^#`-part of the sharp sum already contributes `(|P|−1)·‖α(1)‖²` (`|P| = p^q` by
`card_P_eq`), and `α` vanishes off `H` so the ambient `↥S`-sum *is* the `H`-filtered sum. -/
theorem H_sharp_alphaFun_inflation [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) :
    ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ‖H_sharp_alphaFun hG hyp χ 1‖ ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖H_sharp_alphaFun hG hyp χ x‖ ^ 2 := by
  classical
  set α := H_sharp_alphaFun hG hyp χ with hαdef
  -- The core bound over all of `↥S`.
  have hcore := sum_normSq_erase_one_ge_of_const_on_subgroup (hyp.P.subgroupOf hyp.S) α
    (H_sharp_alphaFun_const_on_P hG hyp χ)
  -- `|P.subgroupOf S| = |P| = p^q`.
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hcard : Nat.card ↥(hyp.P.subgroupOf hyp.S) = hyp.p ^ hyp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
    exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  -- The ambient sum equals the `H`-filtered sum (`α` vanishes off `H`).
  have hsupp : ∑ x : ↥hyp.S, ‖α x‖ ^ 2
      = ∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S), ‖α x‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ hyp.H.subgroupOf hyp.S)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ hyp.H.subgroupOf hyp.S), ‖α x‖ ^ 2
        = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hαdef, H_sharp_alphaFun_eq_zero_of_not_mem hG hyp χ x (Finset.mem_filter.mp hx).2]
      simp
    rw [h0, add_zero]
  -- The sharp sum is the filtered sum minus the identity term.
  have h1mem : (1 : ↥hyp.S) ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hyp.H.subgroupOf hyp.S).one_mem⟩
  have hsharp : ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1, ‖α x‖ ^ 2
      = (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S), ‖α x‖ ^ 2) - ‖α 1‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ h1mem]
    ring
  rw [hsharp, ← hsupp]
  calc ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ‖α 1‖ ^ 2
      = ((Nat.card ↥(hyp.P.subgroupOf hyp.S) : ℝ) - 1) * ‖α 1‖ ^ 2 := by
        rw [hcard]
        congr 1
        have h1 : (1 : ℕ) ≤ hyp.p ^ hyp.q :=
          Nat.one_le_pow _ _ (by have := hyp.three_le_p; omega)
        rw [Nat.cast_sub h1]
        norm_num
    _ ≤ (∑ x : ↥hyp.S, ‖α x‖ ^ 2) - ‖α 1‖ ^ 2 := hcore

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.5.a) correction as a class function on `↥S`**: `H_sharp_alphaFun` is the
underlying function of the `ℂ`-combination `∑_{i≥1, P⊆ker ζ_i} (c̄_i/‖ζ_i‖²) • ζ_i`. -/
noncomputable def H_sharp_alphaCF [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) : ClassFunction ↥hyp.S ℂ :=
  ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
        (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
        (H_sharp_hypothesis76 hG hyp).zetaNormSq i) • (H_sharp_hypothesis76 hG hyp).zeta i

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
@[simp] theorem H_sharp_alphaCF_apply [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) (a : ↥hyp.S) :
    H_sharp_alphaCF hG hyp χ a = H_sharp_alphaFun hG hyp χ a := by
  rw [H_sharp_alphaCF, H_sharp_alphaFun,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [ClassFunction.smul_apply])

/-- `H = PC` is normal in `S` (it is the Fitting subgroup, `H_eq_fittingInG`) — as an
instance on the `subgroupOf` form, so that `conjBy`/`inertia` statements over `↥S` elaborate. -/
instance H_sharp_subgroupOf_normal (hyp : Hypothesis (G := G)) :
    (hyp.H.subgroupOf hyp.S).Normal := by
  rw [hyp.H_eq_fittingInG]
  exact OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal hyp.S

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Restriction of a (7.6) family member is `‖ζ_j‖²` times its conjugate-orbit sum**
(extraction of the Mackey computation shared by the ZIrr-membership and the (13.5.a)
inner-product orthogonality): there is an inducing irreducible `θ` with
`ζ_j = Ind_K^S θ` and `Res_K ζ_j = ‖ζ_j‖² • ∑_{ψ ∈ orbit(θ)} ψ`. -/
theorem H_sharp_restrict_zeta_eq_orbitSum [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin ((H_sharp_hypothesis76 hG hyp).n + 1)) :
    ∃ θ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S),
      (H_sharp_hypothesis76 hG hyp).zeta j
        = ClassFunction.induce ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
            (θ : ClassFunction ↥((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S) ℂ) ∧
      (haveI : ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S).Normal :=
        H_sharp_subgroupOf_normal hyp
      ClassFunction.restrict ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
          ((H_sharp_hypothesis76 hG hyp).zeta j)
        = (H_sharp_hypothesis76 hG hyp).zetaNormSq j •
            ∑ ψ ∈ Finset.univ.image (fun x : ↥hyp.S =>
              ClassFunction.conjBy x⁻¹
                (θ : ClassFunction ↥((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S) ℂ)), ψ) := by
  classical
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  haveI hKnorm : K.Normal := H_sharp_subgroupOf_normal hyp
  obtain ⟨θ₀, hθ₀⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced j
  have hθ : (H_sharp_hypothesis76 hG hyp).zeta j
      = ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) := by
    rw [hθ₀]
  refine ⟨θ₀, hθ, ?_⟩
  have hK0 : (Nat.card ↥K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have horbit := OddOrder.RepresentationTheory.card_smul_restrict_induce_eq_inertia_smul_orbitSum
    (G := ↥hyp.S) (H := K) (k := ℂ) (θ₀ : ClassFunction ↥K ℂ)
  have hinertia := OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
    (G := ↥hyp.S) (H := K) θ₀
  have hnormval : (Nat.card ↥K : ℂ) * (H_sharp_hypothesis76 hG hyp).zetaNormSq j
      = (Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
          (θ₀ : ClassFunction ↥K ℂ)) : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hθ]
    exact hinertia
  have hIKnorm : ((Nat.card ↥K : ℂ))⁻¹ * (Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
      (θ₀ : ClassFunction ↥K ℂ)) : ℂ) = (H_sharp_hypothesis76 hG hyp).zetaNormSq j := by
    rw [← hnormval]
    field_simp
  have h1 : (Nat.card ↥K : ℂ) • ClassFunction.restrict K
      ((H_sharp_hypothesis76 hG hyp).zeta j)
      = ((Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
          (θ₀ : ClassFunction ↥K ℂ)) : ℕ) : ℂ) • ∑ ψ ∈ Finset.univ.image
            (fun x : ↥hyp.S => ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ)] at horbit
    rw [hθ]
    exact horbit
  have h2 := congrArg (fun φ => ((Nat.card ↥K : ℂ))⁻¹ • φ) h1
  simp only [smul_smul, inv_mul_cancel₀ hK0, one_smul] at h2
  rw [h2, hIKnorm]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **Restriction of the (13.5.a) correction as a combination of family restrictions**
(pointwise linearity; extraction shared by the ZIrr-membership and the inner-product
orthogonality). -/
theorem H_sharp_restrict_alphaCF_decomp [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) :
    ClassFunction.restrict ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
        (H_sharp_alphaCF hG hyp χ)
      = ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
            (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
              OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
          (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
            (H_sharp_hypothesis76 hG hyp).zetaNormSq i) •
            ClassFunction.restrict ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
              ((H_sharp_hypothesis76 hG hyp).zeta i) := by
  classical
  ext x
  rw [ClassFunction.restrict_apply, H_sharp_alphaCF,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply, ClassFunction.restrict_apply])

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **`(1/‖ζ_i‖²)·Res_H ζ_i` is a virtual character of `H`** — the "`Res ζ_i/‖ζ_i‖²` is a
character" step of Peterfalvi (13.5.a).  `ζ_i = Ind_K^S θ_i` (`zeta_induced`), so by the Mackey
orbit form (`card_smul_restrict_induce_eq_inertia_smul_orbitSum`) and the inertia norm
(`card_mul_inner_self_induce_eq_card_inertia`), `Res_K ζ_i = ‖ζ_i‖² · (sum of the distinct
conjugates of θ_i)` — an ℕ-combination of irreducibles (`orbitSum_mem_ZIrr`). -/
theorem H_sharp_inv_normSq_restrict_zeta_mem_ZIrr [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (i : Fin ((H_sharp_hypothesis76 hG hyp).n + 1)) :
    ((H_sharp_hypothesis76 hG hyp).zetaNormSq i)⁻¹ •
        ClassFunction.restrict ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
          ((H_sharp_hypothesis76 hG hyp).zeta i)
      ∈ ZIrr ↥((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S) := by
  classical
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  haveI hKnorm : K.Normal := H_sharp_subgroupOf_normal hyp
  obtain ⟨θ₀, hθ₀⟩ := (H_sharp_hypothesis76 hG hyp).zeta_induced i
  -- Re-type across the definitional equality `(H_sharp_hypothesis76 hG hyp).H = hyp.H`, and
  -- bridge the canonical `Fintype`/`Invertible` instances (both subsingleton classes).
  have hθ : (H_sharp_hypothesis76 hG hyp).zeta i
      = ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) := by
    rw [hθ₀]
  -- The Mackey orbit form, divided by `|K|`.
  have hK0 : (Nat.card ↥K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have horbit := OddOrder.RepresentationTheory.card_smul_restrict_induce_eq_inertia_smul_orbitSum
    (G := ↥hyp.S) (H := K) (k := ℂ) (θ₀ : ClassFunction ↥K ℂ)
  have hinertia := OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
    (G := ↥hyp.S) (H := K) θ₀
  -- `‖ζ_i‖² ≠ 0` (it is `|I|/|K|` with `|I| ≥ 1`).
  have hnormval : (Nat.card ↥K : ℂ) * (H_sharp_hypothesis76 hG hyp).zetaNormSq i
      = (Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
          (θ₀ : ClassFunction ↥K ℂ)) : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hθ]
    exact hinertia
  have hI0 : (Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
      (θ₀ : ClassFunction ↥K ℂ)) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hnorm0 : (H_sharp_hypothesis76 hG hyp).zetaNormSq i ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnormval
    exact hI0 hnormval.symm
  -- `Res ζ_i = ‖ζ_i‖² • orbitSum θ₀`, hence `(1/‖ζ_i‖²)·Res ζ_i` is the orbit sum.
  have hIKnorm : ((Nat.card ↥K : ℂ))⁻¹ * (Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
      (θ₀ : ClassFunction ↥K ℂ)) : ℂ) = (H_sharp_hypothesis76 hG hyp).zetaNormSq i := by
    rw [← hnormval]
    field_simp
  have hres : ClassFunction.restrict K ((H_sharp_hypothesis76 hG hyp).zeta i)
      = (H_sharp_hypothesis76 hG hyp).zetaNormSq i •
          ∑ ψ ∈ Finset.univ.image (fun x : ↥hyp.S =>
            ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
    have h1 : (Nat.card ↥K : ℂ) • ClassFunction.restrict K
        ((H_sharp_hypothesis76 hG hyp).zeta i)
        = ((Nat.card ↥(ClassFunction.inertia (G := ↥hyp.S)
            (θ₀ : ClassFunction ↥K ℂ)) : ℕ) : ℂ) • ∑ ψ ∈ Finset.univ.image
              (fun x : ↥hyp.S => ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
      rw [← Nat.cast_smul_eq_nsmul (R := ℂ)] at horbit
      rw [hθ]
      exact horbit
    have h2 := congrArg (fun φ => ((Nat.card ↥K : ℂ))⁻¹ • φ) h1
    simp only [smul_smul, inv_mul_cancel₀ hK0, one_smul] at h2
    rw [h2, hIKnorm]
  have hmain : ((H_sharp_hypothesis76 hG hyp).zetaNormSq i)⁻¹ •
      ClassFunction.restrict K ((H_sharp_hypothesis76 hG hyp).zeta i)
      = ∑ ψ ∈ Finset.univ.image (fun x : ↥hyp.S =>
          ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
    rw [hres, smul_smul, inv_mul_cancel₀ hnorm0, one_smul]
  rw [hmain]
  exact OddOrder.RepresentationTheory.orbitSum_mem_ZIrr (G := ↥hyp.S) θ₀

/-- **`H = PC` is abelian** (Peterfalvi (13.2.a,b)): `P` is (elementary) abelian
(`basic_structure`), `C ≤ U` is abelian (`S_U_commutative`), and `C` centralizes `P`
(`C = U ⊓ C_S(P)`), so the join is abelian (`isMulCommutative_sup_of_le_centralizer`).
The `habelian` input of the (13.7) Parseval bookkeeping. -/
theorem Hypothesis.H_mulCommutative [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : IsMulCommutative ↥hyp.H := by
  obtain ⟨-, -, hPel, -, -, -⟩ := basic_structure hG hyp
  have hPab : IsMulCommutative ↥hyp.P := ⟨⟨hPel.1⟩⟩
  have hCab : IsMulCommutative ↥hyp.C := by
    have hCU : hyp.C ≤ hyp.U := hyp.C_eq ▸ inf_le_left
    exact ⟨⟨fun a b => Subtype.ext (by
      have h := hyp.S_U_commutative.is_comm.comm
        (⟨(a : G), hCU a.2⟩ : ↥hyp.U) ⟨(b : G), hCU b.2⟩
      simpa using congrArg Subtype.val h)⟩⟩
  have hCP : hyp.C ≤ Subgroup.centralizer (hyp.P : Set G) := hyp.C_eq ▸ inf_le_right
  change IsMulCommutative ↥(hyp.P ⊔ hyp.C)
  rw [sup_comm]
  exact OddOrder.BG.Ch4.S15.isMulCommutative_sup_of_le_centralizer hCab hPab hCP

/-- **`P` centralizes every element of `H = PC`** (Peterfalvi (13.4), disjointness ingredient):
for `x ∈ H`, `P ≤ C_G(x)`.  Immediate from `H` abelian (`H_mulCommutative`) and `P ≤ H`.  This is
the first half of the (13.4) conjugate-disjointness `(H^#)^G ∩ (K^#)^G = ∅`: a common point `x`
would have `P ≤ C_G(x) ≤ T^g` (the `A₀(T^g)` TI-property), impossible since `|P| = p^q` exceeds
the `p`-part `p` of `|T|`. -/
theorem Hypothesis.P_le_centralizer_of_mem_H [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {x : G} (hx : x ∈ hyp.H) :
    hyp.P ≤ Subgroup.centralizer ({x} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  have hyH : y ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.P ⊔ hyp.C) hy
  have hcomm := (hyp.H_mulCommutative hG).is_comm.comm (⟨x, hx⟩ : ↥hyp.H) ⟨y, hyH⟩
  simpa using congrArg Subtype.val hcomm


open scoped Classical in
/-- **Sharp-set Parseval bookkeeping** (the `s + d² = |H|·n` shape of Peterfalvi (13.7)): for a
function `f` agreeing on `K` with a class function `ψ` of self inner product `n`, the
squared-norm sum over the nonidentity `K`-members is `|K|·n − ‖f(1)‖²`. -/
theorem sum_filter_erase_one_normSq_eq {L : Type*} [Group L] [Fintype L]
    {K : Subgroup L} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (f : L → ℂ) (ψ : ClassFunction ↥K ℂ) (hagree : ∀ k : ↥K, f ↑k = ψ k)
    {n : ℕ} (hn : ClassFunction.inner ψ ψ = (n : ℂ)) :
    ∑ x ∈ (Finset.univ.filter (· ∈ K)).erase 1, ‖f x‖ ^ 2
      = (Nat.card ↥K : ℝ) * (n : ℝ) - ‖f 1‖ ^ 2 := by
  classical
  -- The full `K`-sum is `|K|·n` (Parseval on `↥K`).
  have htotal : ∑ x ∈ Finset.univ.filter (· ∈ K), ‖f x‖ ^ 2
      = (Nat.card ↥K : ℝ) * (n : ℝ) := by
    have hbij : ∑ x ∈ Finset.univ.filter (· ∈ K), ‖f x‖ ^ 2 = ∑ k : ↥K, ‖ψ k‖ ^ 2 := by
      refine Finset.sum_bij' (fun x hx => (⟨x, (Finset.mem_filter.mp hx).2⟩ : ↥K))
        (fun k _ => (k : L)) ?_ ?_ ?_ ?_ ?_
      · intro x hx; exact Finset.mem_univ _
      · intro k _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.2⟩
      · intro x hx; rfl
      · intro k _; rfl
      · intro x hx
        rw [hagree ⟨x, (Finset.mem_filter.mp hx).2⟩]
    have hpars : ((∑ k : ↥K, ‖ψ k‖ ^ 2 : ℝ) : ℂ) = (Nat.card ↥K : ℂ) * (n : ℂ) := by
      rw [sum_normSq_eq_card_mul_inner, hn]
    have hpars' : ∑ k : ↥K, ‖ψ k‖ ^ 2 = (Nat.card ↥K : ℝ) * (n : ℝ) := by
      exact_mod_cast hpars
    rw [hbij, hpars']
  have h1mem : (1 : L) ∈ Finset.univ.filter (· ∈ K) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, K.one_mem⟩
  have hsplit : ∑ x ∈ (Finset.univ.filter (· ∈ K)).erase 1, ‖f x‖ ^ 2
      = (∑ x ∈ Finset.univ.filter (· ∈ K), ‖f x‖ ^ 2) - ‖f 1‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ h1mem]
    ring
  rw [hsplit, htotal]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.5.a) correction restricted to `H` is a virtual character of `H`**: with integer
(7.7.a) coefficients `c_i ∈ ℤ` (the `χ ∈ ℤ[Irr G]` case), the `P`-kernel tail
`α = ∑ (c̄_i/‖ζ_i‖²) • ζ_i` restricts to `∑ c_i • ((1/‖ζ_i‖²)·Res ζ_i) ∈ ℤ[Irr H]`
(each normalized restriction is the conjugate-orbit character,
`H_sharp_inv_normSq_restrict_zeta_mem_ZIrr`).  The integrality carrier of Peterfalvi (13.5):
it makes `‖α‖²_H ∈ ℕ` and `α(1) ∈ ℤ` available to the (13.7)/(13.8) Parseval bookkeeping. -/
theorem H_sharp_alphaCF_restrict_mem_ZIrr [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ)
    (hc : ∀ i, ∃ z : ℤ, (H_sharp_hypothesis76 hG hyp).cCoeff χ i = (z : ℂ)) :
    ClassFunction.restrict ((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S)
        (H_sharp_alphaCF hG hyp χ)
      ∈ ZIrr ↥((H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S) := by
  classical
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76 hG hyp).H.subgroupOf hyp.S with hKdef
  -- Restriction is pointwise, so it commutes with the defining sum.
  have hlin : ClassFunction.restrict K (H_sharp_alphaCF hG hyp χ)
      = ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
            (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
              OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
          (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
            (H_sharp_hypothesis76 hG hyp).zetaNormSq i) •
            ClassFunction.restrict K ((H_sharp_hypothesis76 hG hyp).zeta i) := by
    ext x
    rw [ClassFunction.restrict_apply, H_sharp_alphaCF,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [ClassFunction.smul_apply, ClassFunction.smul_apply, ClassFunction.restrict_apply])
  rw [hlin]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  obtain ⟨z, hz⟩ := hc i
  rw [hz, star_intCast, div_eq_mul_inv, mul_smul, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ z (H_sharp_inv_normSq_restrict_zeta_mem_ZIrr hG hyp i)

/-! ### The (13.10) atoms

The Core (13.6)–(13.9) relayers use shared rational atoms: `slam`/`seta` are the `G₀`
squared-norm sums of `λ^{τ₁}`/`η₁₀` (rational by the Galois integrality
`OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed`), and `g0`/`HS` are counting
ratios.  Materializing them here lets the downstream Core relayer state each estimate over the
same exact quantities without introducing an opaque cascade carrier. -/

/-- The generic set `G₀` of (13.9) as a `Finset`. -/
noncomputable def Hypothesis.G0Finset [Finite G] (hyp : Hypothesis (G := G)) : Finset G :=
  (Set.toFinite hyp.G0).toFinset

open scoped Classical in
/-- **The squared-norm sum `Σ_{x∈A}‖χ(x)‖²` as a rational number** — defined as the natural
number it equals when the Galois-integrality applies (`χ ∈ ℤ[Irr]`, `A` cyclic-closed:
`exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed`), and junk `0` otherwise.  The (13.10) atoms
`slam`/`seta` are `normSqSumQ G₀ χ / |G|`. -/
noncomputable def normSqSumQ {H : Type*} [Group H] (A : Finset H) (χ : ClassFunction H ℂ) : ℚ :=
  if h : ∃ n : ℕ, (n : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2 then ((Classical.choose h : ℕ) : ℚ) else 0

/-- The defining property of `normSqSumQ` on its good domain. -/
theorem normSqSumQ_spec {H : Type*} [Group H] {A : Finset H} {χ : ClassFunction H ℂ}
    (h : ∃ n : ℕ, (n : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2) :
    ((normSqSumQ A χ : ℚ) : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2 := by
  rw [normSqSumQ, dif_pos h]
  exact_mod_cast Classical.choose_spec h

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical FiniteInduce in
/-- **Peterfalvi (13.3.a)**: each nonzero `μ`-column sum `μ_j = ∑_i μ_{ij}` is induced from a
*linear* (degree-one) irreducible character of `H = PC`.

This is the honest statement of the `CharacterDegreeData.mu_j_linear_induced` field
(materializing (13.3.a) at the `S`-instance).  Assembly of the campaign pieces: `μ_j` lies in
the §9 family `𝒮(H₀)` (`mu_colSum_mem_sOf_H0`) and is reducible (`mu_colSum_not_irreducible`, a
sum of `q ≥ 2` distinct irreducibles), so the case-agnostic §9 `isIndHC`
(`reducible_sOf_H0_isIndHC`) gives `μ_j = Ind_{HC}(ψ)` with `ψ` linear irreducible; the `M`-level
`HC` is `(H ⊔ C).subgroupOf S = (PC).subgroupOf S` (`hcRealized_map_subtype_eq`,
`toTypesIIIIIIVSetupS_cSub_eq_C`, `H = P ⊔ C`), through which `ψ` transports to the required `θ`
on `hyp.H.subgroupOf hyp.S`. -/
theorem Hypothesis.mu_j_isIndPC [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
        (∑ i : Fin hyp.q, hyp.mu i j)
          = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ := by
  classical
  haveI := hyp.finiteG
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  letI : Fintype ↥(OddOrder.Peterfalvi.S11.huSub data) := Fintype.ofFinite _
  letI : Fintype ↥(OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)) := Fintype.ofFinite _
  letI : Fintype ↥((OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)).map
      (OddOrder.Peterfalvi.S11.huSub data).subtype) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card ↥((OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)).map
      (OddOrder.Peterfalvi.S11.huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `μ_j ∈ 𝒮(H₀)`, reducible → `isIndHC`
  have hmem := hyp.mu_colSum_mem_sOf_H0 hG chief j hj
  have hred := hyp.mu_colSum_not_irreducible j
  obtain ⟨ψ, hψirr, hψone, hψeq⟩ :=
    OddOrder.Peterfalvi.S11.reducible_sOf_H0_isIndHC hG (hyp.mkSection11CharacterDataS hG chief)
      hmem hred
  -- `HC.map subtype = (H ⊔ C).subgroupOf S = (PC).subgroupOf S = hyp.H.subgroupOf S`
  have hHeq : data.H = hyp.P := by change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hsupeq : data.H ⊔ OddOrder.Peterfalvi.S11.cSub data chief = hyp.H := by
    rw [hHeq, hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]; rfl
  have hHC : (OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)).map (OddOrder.Peterfalvi.S11.huSub data).subtype
      = hyp.H.subgroupOf hyp.S := by
    rw [OddOrder.Peterfalvi.S11.hcRealized_map_subtype_eq chief, hsupeq]
  -- transport `ψ` back to `hyp.H.subgroupOf S`
  set θ := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ with hθdef
  refine ⟨θ, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθdef, ClassFunction.compHom_apply, map_one, hψone]
  · rw [hψeq, hθdef,
      OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ]

/-- The distinguished `η₁₀ = τ₃(ω₁₀)` of the (13.7)/(13.9) estimates. -/
noncomputable def Hypothesis.eta10 (hyp : Hypothesis (G := G)) : ClassFunction G ℂ :=
  hyp.eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩

open scoped FiniteInduce in
/-- **`η₁₀` is a virtual character of `G`** — real content of the 3002-threaded grid:
`η₁₀ = τ₃(ω₁₀)` (`eta_eq_tau_omega`), `ω₁₀ ∈ ZIrr W` (`omega_mem_ZIrr`), and `τ₃` preserves
virtual characters (`tau3_mem_ZIrr`). -/
theorem Hypothesis.eta10_mem_ZIrr [Finite G] (hyp : Hypothesis (G := G)) :
    hyp.eta10 ∈ ZIrr G := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
  exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)

/-- **Regularity of mixed products**: for `x ∈ W₁ ∖ {1}` and `y ∈ W₂ ∖ {1}` the product `x·y`
avoids `W₁ ∪ W₂` — otherwise one factor would lie in `W₁ ⊓ W₂ = ⊥`.  The membership feed of
`tau3_apply_of_regular` in the (1.10) congruence computations. -/
theorem Hypothesis.mul_notMem_W1_union_W2 (hyp : Hypothesis (G := G))
    {x y : G} (hx : x ∈ hyp.W1) (hy : y ∈ hyp.W2) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x * y ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := by
  rintro (hmem | hmem)
  · have hyW1 : y ∈ hyp.W1 := by
      have h := mul_mem (inv_mem hx) hmem
      rwa [inv_mul_cancel_left] at h
    have hbot : y ∈ hyp.W1 ⊓ hyp.W2 := ⟨hyW1, hy⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
    exact hy1 hbot
  · have hxW2 : x ∈ hyp.W2 := by
      have h := mul_mem hmem (inv_mem hy)
      rwa [mul_inv_cancel_right] at h
    have hbot : x ∈ hyp.W1 ⊓ hyp.W2 := ⟨hx, hxW2⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
    exact hx1 hbot

/-- **Peterfalvi (13.7), the (1.10) congruence for `η₁₀`**: for `y ∈ W₂^#`,
`η₁₀(y) ≡ 1 (mod (1 − ε))` in the algebraic integers, `ε` a primitive `q`-th root of unity.

Route: pick `x ∈ W₁^#`; `x` commutes with `y`, `x^q = 1`, and `η₁₀ ∈ ℤ[Irr G]`, so the
(1.10.a) congruence (`exists_integral_apply_sub_of_commute`) gives `η₁₀(xy) ≡ η₁₀(y)`.  The
product `xy` is `τ₃`-regular (`mul_notMem_W1_union_W2`), so `η₁₀(xy) = ω₁₀(xy)` ((3.2.c));
the (3.3) grid semantics factorize `ω₁₀(xy) = ω₁₀(x)·ω₁₀(y) = ω₁₀(x)` (issue 2033:
`omega_mul`, `omega_col_zero_apply_of_mem_W2`), a `q`-th root of unity
(`omega_pow_q_of_mem_W1`), which is `≡ 1 (mod (1 − ε))` by the geometric-sum identity. -/
theorem Hypothesis.eta10_apply_sub_one_integral [Finite G] (hyp : Hypothesis (G := G))
    {ε : ℂ} (hε : IsPrimitiveRoot ε hyp.q) {y : G} (hyW2 : y ∈ hyp.W2) (hy1 : y ≠ 1) :
    ∃ z : ℂ, IsIntegral ℤ z ∧ hyp.eta10 y - 1 = (1 - ε) * z := by
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  -- pick `x ∈ W₁^#`
  obtain ⟨x, hxW1, hx1⟩ : ∃ x : G, x ∈ hyp.W1 ∧ x ≠ 1 := by
    haveI : Nontrivial ↥hyp.W1 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.q_eq_card_W1]; exact hyp.q_prime.one_lt)
    obtain ⟨x', hx'⟩ := exists_ne (1 : ↥hyp.W1)
    exact ⟨x', x'.2, fun h => hx' (Subtype.ext h)⟩
  -- `x^q = 1`
  have hxq : x ^ hyp.q = 1 := by
    have h1 : (⟨x, hxW1⟩ : ↥hyp.W1) ^ hyp.q = 1 := by
      rw [hyp.q_eq_card_W1]; exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
  -- (1.10.a): `η₁₀(xy) − η₁₀(y) = (1 − ε)·z₁`
  obtain ⟨z₁, hz₁int, hz₁⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hyp.eta10_mem_ZIrr hxq (hyp.W1_commutes_W2 x hxW1 y hyW2)
  -- `τ₃`-regular value: `η₁₀(xy) = ω₁₀(xy)`
  have hxyW : x * y ∈ hyp.W := mul_mem (hW1W hxW1) (hW2W hyW2)
  have hreg : hyp.eta10 (x * y)
      = hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x * y, hxyW⟩ := by
    rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
    exact hyp.tau3_apply_of_regular _ _ hxyW (hyp.mul_notMem_W1_union_W2 hxW1 hyW2 hx1 hy1)
  -- factorize: `ω₁₀(xy) = ω₁₀(x)·ω₁₀(y) = ω₁₀(x)` (issue-2033 grid semantics)
  have hfact : hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x * y, hxyW⟩
      = hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x, hW1W hxW1⟩ := by
    have hmul : (⟨x * y, hxyW⟩ : ↥hyp.W) = ⟨x, hW1W hxW1⟩ * ⟨y, hW2W hyW2⟩ := rfl
    rw [hmul, hyp.omega_mul,
      hyp.omega_col_zero_apply_of_mem_W2 _ ⟨y, hW2W hyW2⟩ hyW2, mul_one]
  -- `ω₁₀(x)` is a `q`-th root of unity: `= ε^k`
  have hpow : hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x, hW1W hxW1⟩ ^ hyp.q
      = 1 := hyp.omega_pow_q_of_mem_W1 _ _ ⟨x, hW1W hxW1⟩ hxW1
  haveI : NeZero hyp.q := ⟨hyp.q_prime.pos.ne'⟩
  obtain ⟨k, -, hk⟩ := hε.eq_pow_of_pow_eq_one hpow
  -- `ε^k − 1 = (1 − ε)·z₂` with `z₂` integral (geometric sum)
  have hε_mem : ε ∈ integralClosure ℤ ℂ := hε.isIntegral hyp.q_prime.pos
  have hz₂int : IsIntegral ℤ (-(∑ i ∈ Finset.range k, ε ^ i)) :=
    (Subalgebra.sum_mem _ (fun i _ => Subalgebra.pow_mem _ hε_mem i) :
      IsIntegral ℤ (∑ i ∈ Finset.range k, ε ^ i)).neg
  have hz₂ : ε ^ k - 1 = (1 - ε) * (-(∑ i ∈ Finset.range k, ε ^ i)) := by
    rw [← geom_sum_mul ε k]; ring
  -- combine: `η₁₀(y) − 1 = (η₁₀(xy) − (1−ε)z₁) − 1 = (ε^k − 1) − (1−ε)z₁`
  refine ⟨-(∑ i ∈ Finset.range k, ε ^ i) - z₁, hz₂int.sub hz₁int, ?_⟩
  have hyval : hyp.eta10 y = hyp.eta10 (x * y) - (1 - ε) * z₁ := by linear_combination -hz₁
  rw [hyval, hreg, hfact, ← hk]
  linear_combination hz₂

/-! ### The (13.9)/(13.10) counting layer

The Parseval estimates (13.10.1)/(13.10.2) and the disjoint-cover count (13.10.3) rest on one
counting skeleton: `G` splits as `{1} ⊔ G₀ ⊔ (H^#)^G ⊔ (Q^#)^G` — the two saturations are
disjoint (element orders: `q ∤ |H|` while every nonidentity element of `Q` has order a positive
power of `q`) — and a conjugation-invariant sum over a saturation collapses to `[G : N]` times
the local sum (`IsTISubset.sum_conjClassSet`, issue 9011).  The `H`-side TI input is the proven
`H_sharp_isTISubset`; the `Q`-side is its `T`-mirror below. -/

end OddOrder.Peterfalvi.S15
