/-
# Peterfalvi §7 — discharging the `(7.7.a)`/`(7.8.c)` certificates of `S09`

`S09_NonexistenceCertain.lean` carries Peterfalvi's `(7.7.a)` (`Hypothesis76.chiRho_decomp`) and
`(7.8.c.i)` (`Hypothesis78.chiRho_eq_inner_beta`) as structural certificate fields: deriving them
needs the `CF(L,A)`-basis argument of Peterfalvi (7.7), whose foundation is the **spanning
identity** formalized here.

This file lives outside `S09` (which is concurrently edited for the `(7.11)` assembly) to avoid
conflicts; it imports the `S09` machinery and supplies standalone lemmas toward the certificate
discharge (issue 1013).
-/
import OddOrder.Peterfalvi.S09_BetaDecompOrthogonality

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S09_CertificateDischarge` (2000-line limit, issue 0103 第 2
パス).
-/
namespace OddOrder.Peterfalvi.S09.Cert
open OddOrder.RepresentationTheory
open scoped Classical

variable {L : Type*} [Group L] [Fintype L]



/-- **Discharge of the (7.8.c.i) certificate for an induced family** (Peterfalvi (7.8.c)).  With the
distinguished `ζ = Ind_K^L θ_0` at index `0` (so the induced principal character `Ind_K^L 1_K` is at
some `ind1H ≠ 0`), `χ` orthogonal to `S^ν` (`hortho`), and the coherence agreement
`(ζ_i − d_i ζ_0)^τ = ζ_i^ν − d_i ζ_0^ν` for the non-distinguished, non-`ind1H` indices (`hagree`),
the `(7.7.a)` decomposition collapses to the single `ind1H` term: every other coefficient vanishes
(`inner_sub_smul_left_eq_zero`), and the surviving term simplifies via `ζ_{ind1H}(x) = ‖ζ_{ind1H}‖²`
(`induce_trivialChar_apply_eq_index`/`_normSq_eq_index`, both `= [L:K]`).  Hence
`χ^ρ(x) = star((ζ_{ind1H} − d_{ind1H} ζ_0)^τ, χ)`; with `d_{ind1H} = 1` this is `star(β,χ)`. -/
theorem chiRho_eq_inner_beta_induced {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) (K : Subgroup ↥L) [K.Normal] [Finite ↥K]
    [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K) (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hdeg : ∀ i, ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥L)
        = d i * ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥L))
    (hAconj : ∀ g h : ↥L, h * g * h⁻¹ ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L ↔
      g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hAK_off : ∀ y : ↥L, y ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L → y ∈ K)
    (hA_one : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K)
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ) (χ : ClassFunction G ℂ)
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩
        = ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
          - d i • ν (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)))
    (hortho : ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.inner χ (ν (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))) = 0)
    {x : ↥L} (hx : (x : G) ∈ A) :
    H71.chiRho χ x = star (ClassFunction.inner (H71.τ
      ⟨ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
          - d ind1H • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ),
        psi_support ind1H⟩) χ) := by
  classical
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  rw [chiRho_decomp_induced H71 K θ d psi_support hinj hcover hdeg hAconj hAK_off hA_one χ hx]
  have hxK : x ∈ K := hAK_off x (by rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; exact hx)
  refine sum_collapse_to_single (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
    (fun i => ClassFunction.inner (H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩) χ)
    (Fin.pos_iff_ne_zero.mpr hind1H) ?_ ?_ (induce_norm_ne_zero K (θ ind1H))
  · -- the non-`ind1H` coefficients vanish by coherence
    intro i hi hne
    show ClassFunction.inner (H71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩) χ = 0
    rw [hagree i (Finset.mem_Ioi.mp hi).ne' hne]
    exact inner_sub_smul_left_eq_zero (hortho i hne) (hortho 0 (Ne.symm hind1H))
  · -- the distinguished term: `ζ_{ind1H}(x) = ‖ζ_{ind1H}‖² = [L:K]`
    show ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ) x
      = ClassFunction.inner (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ))
          (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ))
    rw [hzeta_ind1H,
      show ((trivialIrreducibleCharacter ↥K : IrreducibleCharacter ↥K) : ClassFunction ↥K ℂ)
        = trivialClassFunction ↥K from rfl,
      induce_trivialChar_apply_eq_index K hxK, induce_trivialChar_normSq_eq_index K]

/-- **Construction of `Hypothesis78` from coherence data** (Peterfalvi (7.8)).  Given the
`(7.1)`/`(7.6)` data (`H71`, `hτ`, `H ⊴ L`, `A = H^#`), an enumerating family `θ` of the distinct
induced characters with the **distinguished** member `ζ` at index `0` and the induced principal
`Ind 1_H` at `ind1H`, together with the **coherence inputs** of `(7.8)` — the coherent isometric
extension `ν` and the agreement `τ(ψ_i) = ν ζ_i − d_i ν ζ_0` on `S` — the entire `Hypothesis78`
structure is built, *including* the `(7.8.c.i)` certificate `chiRho_eq_inner_beta`, which is
discharged by `chiRho_eq_inner_beta_induced`.

The distinguished `ζ = ζ_0` has `ζ(1) = (Ind 1_H)(1)` (`hdeg_match`), forcing `d_{ind1H} = 1`, so
the
certificate's `β = τ(Ind 1_H − ζ)` matches the family-difference `τ(ζ_{ind1H} − ζ_0)`.  Together
with
`hypothesis76OfFamily` this realizes the issue-1013 goal: `Hypothesis78` (the §7 floor cited by
`(12.16)` / `(14.11)`) is constructible from `(7.1)` + coherence alone, with no certificate assumed. -/
noncomputable def hypothesis78OfDade
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    [Fintype ↥(H.subgroupOf L)] [Invertible (Nat.card ↥(H.subgroupOf L) : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥(H.subgroupOf L))
    (hinj : Function.Injective
      (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ) ∈
        Set.range (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
        - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdeg : ∀ i, ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
        = d i * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥(H.subgroupOf L))
    (hdeg_match : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) (1 : ↥L))
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
          (ν (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          - d i • ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))) :
    Hypothesis78 G A L := by
  classical
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  -- `d_{ind1H} = 1` from the degree match `ζ_0(1) = ζ_{ind1H}(1)`.
  have hz0 : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (θ 0)
  have hd1 : d ind1H = 1 := by
    have h := hdeg ind1H
    rw [← hdeg_match] at h
    have h2 : d ind1H * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = 1 * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) := by
      rw [one_mul, ← h]
    exact mul_right_cancel₀ hz0 h2
  -- `ζ_{ind1H} − ζ_0` is supported on `A` (difference of induced characters of equal degree).
  have hdiff : (ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ)
      - ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    have h := induce_diff_support (θ ind1H) (θ 0) 1 (by rw [one_mul, ← hdeg_match])
    rw [one_smul] at h
    refine h.trans ?_
    intro x hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_iff H hAH x).mpr
      ⟨hx.1, fun h1 => hx.2 (OneMemClass.coe_eq_one.mp h1)⟩
  refine
    { hyp76 := hypothesis76OfFamily H71 hτ H hHL hHnorm hAH θ hinj hcover
      ind1H := ind1H
      zetaDistinct := 0
      zetaDistinct_ne_ind1H := Ne.symm hind1H
      zeta_one_eq_ind1H_one := hdeg_match
      diff_support := hdiff
      nu := ν
      nu_isometry := hnu_isometry
      chiRho_eq_inner_beta := fun χ _ hortho {x} hx => by
        -- Reduce `hyp76.hyp71` to `H71` (`rfl`) so `chiRho_eq_inner_beta_induced` rewrites the LHS.
        rw [show (hypothesis76OfFamily H71 hτ H hHL hHnorm hAH θ hinj hcover).hyp71 = H71 from rfl,
          chiRho_eq_inner_beta_induced H71 (H.subgroupOf L) θ d psi_support hinj hcover hdeg
            (supportInSubgroup_sharp_conj_mem_iff H hAH hHnorm)
            (fun y => supportInSubgroup_sharp_subset_subgroupOf H hAH)
            (one_not_mem_supportInSubgroup_sharp H hAH) ind1H hind1H hzeta_ind1H ν χ hagree hortho
                hx]
        -- Bridge the `(7.7.a)` coefficient `d_{ind1H}` (`= 1`) to the bare difference
        -- `ζ_{ind1H} − ζ_0`.
        refine congrArg star (congrArg (ClassFunction.inner · χ) (congrArg H71.τ ?_))
        apply Subtype.ext
        change ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ)
            - d ind1H • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) = _
        rw [hd1, one_smul]
        rfl }

/-- **Integrality of the `(7.8.a)` coefficient `a`** (Peterfalvi (7.8.a)).  The weighted-sum
coefficient `a = (β, ζ_0^ν) + 1` is an integer: `β = τ(Ind 1_H − ζ)` is a virtual character (from
`(2.6.b)` Dade preservation, packaged in `beta_mem_ZIrr_of_sourceDiff_mem_ZIrr`, given the source
difference `Ind 1_H − ζ ∈ ℤ[Irr L]`), `ζ_0^ν = ν ζ ∈ ℤ[Irr G]` is the coherent image
(`nu_mem_ZIrr_of_isCoherent`), and `inner_mem_ZIrr_int` makes their inner product an integer.
Supplies the `a : ℤ` field of `BetaDecomp` together with the displayed value `(β, ζ_0^ν) + 1`. -/
theorem exists_betaDecomp_a {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L)
    (hdiffZ : H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L)
    (hζ0nuZ : H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G) :
    ∃ a : ℤ, (a : ℂ) = ClassFunction.inner H78.beta
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) + 1 := by
  obtain ⟨m, hm⟩ :=
    ClassFunction.inner_mem_ZIrr_int (H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr hdiffZ) hζ0nuZ
  exact ⟨m + 1, by push_cast; rw [hm]⟩

/-- **Peterfalvi (7.8.b) coefficient identification, generic index** (`case A`, `ζ_0 = ζ`).  For the
`(7.7.a)` coefficient `c_i = (ψ_i^τ, ζ_0^ν)` with `χ = ζ_0^ν` (the distinguished `ζ = ζ_0` at index
`0`), the coherence agreement `ψ_i^τ = ζ_i^ν − d_i ζ_0^ν` (for `i ≠ 0, ind1H`), the isometry of `ν`,
the family orthogonality `(ζ_i, ζ_0) = 0`, the normalization `‖ζ_0‖² = 1`, and `d_i` real, give
`c_i = −d_i`.  This is the off-distinguished coefficient feeding the (7.8.b) double sum. -/
theorem cCoeff_nu_zeta_zero_eq_neg_d {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H76 : Hypothesis76 G A L) (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    {ind1H : Fin (H76.n + 1)}
    (hagree : ∀ i : Fin (H76.n + 1), i ≠ 0 → i ≠ ind1H →
      H76.hyp71.τ (H76.psiSupp i) = ν (H76.zeta i) - H76.d i • ν (H76.zeta 0))
    (hiso : ∀ a b : Fin (H76.n + 1), a ≠ ind1H → b ≠ ind1H →
      ClassFunction.inner (ν (H76.zeta a)) (ν (H76.zeta b))
        = ClassFunction.inner (H76.zeta a) (H76.zeta b))
    (h0ind : (0 : Fin (H76.n + 1)) ≠ ind1H)
    (horth : ∀ i : Fin (H76.n + 1), i ≠ 0 →
      ClassFunction.inner (H76.zeta i) (H76.zeta 0) = 0)
    (hnorm : ClassFunction.inner (H76.zeta 0) (H76.zeta 0) = 1)
    (i : Fin (H76.n + 1)) (hi0 : i ≠ 0) (hind : i ≠ ind1H) :
    H76.cCoeff (ν (H76.zeta 0)) i = - H76.d i := by
  unfold Hypothesis76.cCoeff
  rw [hagree i hi0 hind, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    hiso i 0 hind h0ind, hiso 0 0 h0ind h0ind, horth i hi0, hnorm, mul_one, zero_sub]

/-- **Peterfalvi (7.8.b) coefficient identification, the `Ind 1_H` index.**  At `i = ind1H`, the
`(7.7.a)` coefficient `c_{ind1H} = (ψ_{ind1H}^τ, ζ_0^ν)` equals `(β, ζ_0^ν)`: with `d_{ind1H} = 1`
and `zetaDistinct = 0`, the supported difference `ψ_{ind1H} = ζ_{ind1H} − ζ_0` coincides (as a
member
of `CF(L,A)`) with `Ind 1_H − ζ`, whose Dade image is `β`.  This is the distinguished coefficient
feeding the (7.8.b) double sum; combined with `exists_betaDecomp_a` it gives `c_{ind1H} = a − 1`. -/
theorem cCoeff_nu_zeta_zero_ind1H_eq {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L) (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hzd : H78.zetaDistinct = 0) (hd1 : H78.hyp76.d H78.ind1H = 1) :
    H78.hyp76.cCoeff (ν (H78.hyp76.zeta 0)) H78.ind1H =
      ClassFunction.inner H78.beta (ν (H78.hyp76.zeta 0)) := by
  have hsupp : H78.hyp76.psiSupp H78.ind1H = H78.indMinusZetaSupp := by
    apply Subtype.ext
    simp only [Hypothesis76.psiSupp_coe, Hypothesis78.indMinusZetaSupp, hd1, one_smul, hzd]
  unfold Hypothesis76.cCoeff Hypothesis78.beta
  rw [hsupp]

/-- **Orthogonality collapse of the `(7.7.b)` double sum.**  When the induced family `ζ_i` is
pairwise orthogonal (`(ζ_i, ζ_j) = 0` for `i ≠ j`, true for the distinct induced characters by
Frobenius reciprocity), the `(7.7.b)` double sum splits into a diagonal part and a rank-one
correction:
`‖χ^ρ‖² = Σ_i c̄_i c_i/‖ζ_i‖² − (Σ_i c̄_i ζ_i(1)/‖ζ_i‖²)(Σ_j c_j \overline{ζ_j(1)}/‖ζ_j‖²)/|L|`.
This is the shape used by (7.8.b) (`χ = ζ_0^ν`) before substituting the coefficients. -/
theorem chiRho_norm_sq_collapse {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H76 : Hypothesis76 G A L) (χ : ClassFunction G ℂ)
    (horth : ∀ i j : Fin (H76.n + 1), i ≠ j →
      ClassFunction.inner (H76.zeta i) (H76.zeta j) = 0) :
    ClassFunction.inner (H76.hyp71.chiRhoCF χ) (H76.hyp71.chiRhoCF χ) =
      (∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
        star (H76.cCoeff χ i) * H76.cCoeff χ i / H76.zetaNormSq i)
      - (∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
          star (H76.cCoeff χ i) * H76.zeta i 1 / H76.zetaNormSq i)
        * (∑ j ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
            H76.cCoeff χ j * star (H76.zeta j 1) / H76.zetaNormSq j)
        / (Nat.card L : ℂ) := by
  rw [H76.chiRho_norm_sq_double_sum χ]
  have hsplit : ∀ i j : Fin (H76.n + 1),
      star (H76.cCoeff χ i) * H76.cCoeff χ j / (H76.zetaNormSq i * H76.zetaNormSq j) *
          (ClassFunction.inner (H76.zeta i) (H76.zeta j)
            - H76.zeta i 1 * star (H76.zeta j 1) / (Nat.card L : ℂ)) =
        star (H76.cCoeff χ i) * H76.cCoeff χ j / (H76.zetaNormSq i * H76.zetaNormSq j) *
            ClassFunction.inner (H76.zeta i) (H76.zeta j)
          - (star (H76.cCoeff χ i) * H76.zeta i 1 / H76.zetaNormSq i) *
            (H76.cCoeff χ j * star (H76.zeta j 1) / H76.zetaNormSq j) / (Nat.card L : ℂ) := by
    intro i j; ring
  simp only [hsplit, Finset.sum_sub_distrib]
  congr 1
  · -- diagonal collapse via orthogonality
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i (fun j _ hji => by
        rw [horth i j (Ne.symm hji), mul_zero]) (fun hi' => absurd hi hi')]
    rw [show ClassFunction.inner (H76.zeta i) (H76.zeta i) = H76.zetaNormSq i from rfl]
    field_simp
  · -- rank-one factoring
    rw [Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]

/-- **Diagonal-sum split at `ind1H`** for the (7.8.b) collapse.  Splitting the `Ioi 0` diagonal sum
`Σ_i c̄_i c_i / N_i` at the distinguished index `ind1H`, where `c_{ind1H} = cval` and `c_i = −d_i`
for `i ≠ 0, ind1H`, gives `c̄val·cval/N_{ind1H} + Σ_{i ≠ ind1H} d̄_i d_i / N_i` (the sign cancels).
This isolates the `(a−1)²/e` term from the off-distinguished `d_i`-sum. -/
theorem sum_diag_split_ind1H {n : ℕ} (c N d : Fin (n + 1) → ℂ) (cval : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = cval)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i)) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), star (c i) * c i / N i =
      star cval * cval / N ind1H
        + ∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, star (d i) * d i / N i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr (Fin.pos_iff_ne_zero.mpr hind)), hc_ind1H]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi_ne, hi_ioi⟩ := Finset.mem_erase.mp hi
  rw [hc_rest i (Finset.mem_Ioi.mp hi_ioi).ne' hi_ne, star_neg, neg_mul, mul_neg, neg_neg]

/-- **Arithmetic core of (7.8.b).**  With the collapsed norm `‖ζ^{νρ}‖² = t₁ − X²/(e·h)` where the
diagonal `t₁ = (a−1)²/e + G/e²` and the rank-one `X = (a−1) − G/e`, and the `(1.5.d)` degree-sum
value `G = e(h−1) − e²`, the norm equals the quadratic `u a² − 2 v a + w` of Peterfalvi (7.8.b),
with `u = (1/e)(1−1/h)`, `v = 1/h`, `w = 1 − e/h`.  Pure field identity (verified by `ring`). -/
theorem normEstimate_matching (a e h G : ℝ) (he : e ≠ 0) (hh : h ≠ 0)
    (hG : G = e * (h - 1) - e ^ 2) :
    ((a - 1) ^ 2 / e + G / e ^ 2) - ((a - 1) - G / e) ^ 2 / (e * h) =
      (1 / e) * (1 - 1 / h) * a ^ 2 - 2 * (1 / h) * a + (1 - e / h) := by
  subst hG
  field_simp
  ring

/-- **Diagonal sum evaluation for (7.8.b)** (`term₁`).  With `c_{ind1H} = a−1`, `c_i = −d_i`
(`i ≠ 0, ind1H`), `N_{ind1H} = e`, `d_i = P_i/e`, and `a` / the `d_i` real, the diagonal sum
`Σ_i c̄_i c_i / N_i` evaluates to `(a−1)²/e + (Σ_{i ≠ ind1H} P_i²/N_i)/e²`. -/
theorem term1_eval_generic {n : ℕ} (c N P d : Fin (n + 1) → ℂ) (a e : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = a - 1) (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i))
    (ha1_real : star (a - 1) = a - 1) (hd_real : ∀ i, star (d i) = d i)
    (hd : ∀ i, d i = P i / e) (hN_ind1H : N ind1H = e) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), star (c i) * c i / N i =
      (a - 1) ^ 2 / e
        + (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i) / e ^ 2 := by
  rw [sum_diag_split_ind1H c N d (a - 1) hind hc_ind1H hc_rest, hN_ind1H, ha1_real, ← pow_two]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd_real i, ← pow_two, hd i, div_pow]
  ring

/-- **Rank-one sum evaluation for (7.8.b)** (`X`).  With the same data, the rank-one factor
`Σ_i c̄_i P_i / N_i` evaluates to `(a−1) − (Σ_{i ≠ ind1H} P_i²/N_i)/e` (the `Ind 1_H` term gives
`(a−1)·e/e = a−1`; the off-distinguished terms give `−d_i P_i/N_i = −P_i²/(e N_i)`). -/
theorem rank1_eval_generic {n : ℕ} (c N P d : Fin (n + 1) → ℂ) (a e : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = a - 1) (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i))
    (ha1_real : star (a - 1) = a - 1) (hd_real : ∀ i, star (d i) = d i)
    (hd : ∀ i, d i = P i / e) (hN_ind1H : N ind1H = e) (hP_ind1H : P ind1H = e) (he : e ≠ 0) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), star (c i) * P i / N i =
      (a - 1) - (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i) / e := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr (Fin.pos_iff_ne_zero.mpr hind)),
    hc_ind1H, ha1_real, hP_ind1H, hN_ind1H, mul_div_assoc, div_self he, mul_one, sub_eq_add_neg]
  rw [show (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, star (c i) * P i / N i)
        = ∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i * (-(1 / e)) from
      Finset.sum_congr rfl fun i hi => by
        obtain ⟨hi_ne, hi_ioi⟩ := Finset.mem_erase.mp hi
        rw [hc_rest i (Finset.mem_Ioi.mp hi_ioi).ne' hi_ne, star_neg, hd_real i, hd i]; ring,
    ← Finset.sum_mul]
  ring

/-- **Rank-one sum evaluation, conjugate-weight form** (`Y`).  The collapse's second rank-one
factor `Σ_j c_j \overline{P_j} / N_j` (note: bare `c_j`, conjugated `P_j`) evaluates to the same
`(a−1) − (Σ_{i ≠ ind1H} P_i²/N_i)/e` as `rank1_eval_generic`, using that the degrees `P_i` are real
(`\overline{P_i} = P_i`).  Together with `rank1_eval_generic` this gives `X·Y = ((a−1) − G/e)²`. -/
theorem rank1_eval_Y_generic {n : ℕ} (c N P d : Fin (n + 1) → ℂ) (a e : ℂ)
    {ind1H : Fin (n + 1)} (hind : ind1H ≠ 0)
    (hc_ind1H : c ind1H = a - 1) (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → c i = -(d i))
    (hP_real : ∀ i, star (P i) = P i) (hd : ∀ i, d i = P i / e)
    (hN_ind1H : N ind1H = e) (hP_ind1H : P ind1H = e) (he : e ≠ 0) :
    ∑ i ∈ Finset.Ioi (0 : Fin (n + 1)), c i * star (P i) / N i =
      (a - 1) - (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i) / e := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr (Fin.pos_iff_ne_zero.mpr hind)),
    hc_ind1H, hP_real ind1H, hP_ind1H, hN_ind1H, mul_div_assoc, div_self he, mul_one,
    sub_eq_add_neg]
  rw [show (∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, c i * star (P i) / N i)
        = ∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H, P i ^ 2 / N i * (-(1 / e)) from
      Finset.sum_congr rfl fun i hi => by
        obtain ⟨hi_ne, hi_ioi⟩ := Finset.mem_erase.mp hi
        rw [hc_rest i (Finset.mem_Ioi.mp hi_ioi).ne' hi_ne, hP_real i, hd i]; ring,
    ← Finset.sum_mul]
  ring

/-- **(7.8.b) ℂ-level norm identity.**  Assembling the collapse with the three sum evaluations,
the `ζ_0^ν` self-inner-product equals `(a−1)²/e + G/e² − ((a−1) − G/e)²/|L|` where
`G = Σ_{i ≠ ind1H} ζ_i(1)²/‖ζ_i‖²` is the off-distinguished degree-sum.  (The `.re` and the
`(1.5.d)` value `G = e(h−1)−e²` then yield the (7.8.b) lower bound via `normEstimate_matching`.) -/
theorem zetaNuRho_inner_eq_cexpr {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H76 : Hypothesis76 G A L) (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    {ind1H : Fin (H76.n + 1)} (a e : ℂ) (hind : ind1H ≠ 0)
    (horth : ∀ i j : Fin (H76.n + 1), i ≠ j →
      ClassFunction.inner (H76.zeta i) (H76.zeta j) = 0)
    (hc_ind1H : H76.cCoeff (ν (H76.zeta 0)) ind1H = a - 1)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ ind1H → H76.cCoeff (ν (H76.zeta 0)) i = -(H76.d i))
    (ha1_real : star (a - 1) = a - 1) (hd_real : ∀ i, star (H76.d i) = H76.d i)
    (hP_real : ∀ i, star (H76.zeta i 1) = H76.zeta i 1)
    (hd : ∀ i, H76.d i = H76.zeta i 1 / e)
    (hN_ind1H : H76.zetaNormSq ind1H = e) (hP_ind1H : H76.zeta ind1H 1 = e) (he : e ≠ 0) :
    ClassFunction.inner (H76.hyp71.chiRhoCF (ν (H76.zeta 0)))
        (H76.hyp71.chiRhoCF (ν (H76.zeta 0))) =
      (a - 1) ^ 2 / e
        + (∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase ind1H,
            H76.zeta i 1 ^ 2 / H76.zetaNormSq i) / e ^ 2
        - ((a - 1) - (∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).erase ind1H,
            H76.zeta i 1 ^ 2 / H76.zetaNormSq i) / e) ^ 2 / (Nat.card L : ℂ) := by
  rw [chiRho_norm_sq_collapse H76 (ν (H76.zeta 0)) horth,
    term1_eval_generic (H76.cCoeff (ν (H76.zeta 0))) H76.zetaNormSq (fun i => H76.zeta i 1) H76.d
      a e hind hc_ind1H hc_rest ha1_real hd_real hd hN_ind1H,
    rank1_eval_generic (H76.cCoeff (ν (H76.zeta 0))) H76.zetaNormSq (fun i => H76.zeta i 1) H76.d
      a e hind hc_ind1H hc_rest ha1_real hd_real hd hN_ind1H hP_ind1H he,
    rank1_eval_Y_generic (H76.cCoeff (ν (H76.zeta 0))) H76.zetaNormSq (fun i => H76.zeta i 1) H76.d
      a e hind hc_ind1H hc_rest hP_real hd hN_ind1H hP_ind1H he]
  ring

/-- **(7.8.b) real-part + matching.**  Taking the real part of the ℂ-level norm identity (all of
`a, e, G, |L| = e·h` being real casts) and applying `normEstimate_matching`, the `ζ_0^ν`-norm
equals Peterfalvi's quadratic
`(1/e)(1−1/h)a² − (2/h)a + (1−e/h) = normQuadraticCorrection + (1−e/h)`.
This bridges the ℂ-level `zetaNuRho_inner_eq_cexpr` to the ℝ-valued `NormEstimates` field. -/
theorem cexpr_re_eq_normQuad (a e h G : ℝ) (he : e ≠ 0) (hh : h ≠ 0)
    (hG : G = e * (h - 1) - e ^ 2) :
    (((a : ℂ) - 1) ^ 2 / (e : ℂ) + (G : ℂ) / (e : ℂ) ^ 2
        - (((a : ℂ) - 1) - (G : ℂ) / (e : ℂ)) ^ 2 / ((e : ℂ) * (h : ℂ))).re =
      (1 / e) * (1 - 1 / h) * a ^ 2 - 2 * (1 / h) * a + (1 - e / h) := by
  rw [show (((a : ℂ) - 1) ^ 2 / (e : ℂ) + (G : ℂ) / (e : ℂ) ^ 2
        - (((a : ℂ) - 1) - (G : ℂ) / (e : ℂ)) ^ 2 / ((e : ℂ) * (h : ℂ)))
      = (((a - 1) ^ 2 / e + G / e ^ 2 - ((a - 1) - G / e) ^ 2 / (e * h) : ℝ) : ℂ) from by
      push_cast; ring,
    Complex.ofReal_re, normEstimate_matching a e h G he hh hG]

/-- **(7.8.b) identification** (last mile).  Given the ℂ-level norm identity (`h_inner`, supplied by
`zetaNuRho_inner_eq_cexpr` with `a, e, G` as the real casts `hBD.a`, `complementIndex`, and the
`(1.5.d)` degree-sum value), the real norm `‖ζ_0^{νρ}‖²` equals
`normQuadraticCorrection + (1 − e/h)`.  Fed to `zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq`,
this yields the Peterfalvi (7.8.b) lower bound. -/
theorem zetaNuRhoNormSq_eq_normQuad {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (a_ℝ e_ℝ h_ℝ G_ℝ : ℝ) (he : e_ℝ ≠ 0) (hh : h_ℝ ≠ 0)
    (hG : G_ℝ = e_ℝ * (h_ℝ - 1) - e_ℝ ^ 2)
    (ha : a_ℝ = (hBD.a : ℝ)) (he' : e_ℝ = (H78.complementIndex : ℝ))
    (hh' : h_ℝ = (H78.kernelOrder : ℝ))
    (h_inner : ClassFunction.inner H78.zetaNuRho H78.zetaNuRho =
      ((a_ℝ : ℂ) - 1) ^ 2 / (e_ℝ : ℂ) + (G_ℝ : ℂ) / (e_ℝ : ℂ) ^ 2
        - (((a_ℝ : ℂ) - 1) - (G_ℝ : ℂ) / (e_ℝ : ℂ)) ^ 2 / ((e_ℝ : ℂ) * (h_ℝ : ℂ))) :
    H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD
        + (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)) := by
  unfold OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRhoNormSq
  rw [h_inner, cexpr_re_eq_normQuad a_ℝ e_ℝ h_ℝ G_ℝ he hh hG,
    OddOrder.Peterfalvi.S09.Hypothesis78.normQuadraticCorrection, ha, he', hh']

/-- **(1.5.d) degree-sum over distinct induced characters** (`A = ⊥` specialization of the S08
orbit-count `sum_div_normSq_induce_kernelFilter_eq`).  Summing `χ(1)²/‖χ‖²` over the distinct
nontrivially-induced characters `Ind_K^L θ` (`θ ≠ 1`) gives `[L:K]·(|K| − 1)`.  With `K = H ◁ L`
this is `e·(h − 1)` of Peterfalvi (1.5.d). -/
theorem induce_degree_sum_bot {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    (K : Subgroup L) [K.Normal] [Finite ↥K] [Invertible (Nat.card ↥K : ℂ)] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        θ ≠ trivialIrreducibleCharacter ↥K)).image
        (fun θ => ClassFunction.induce K θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ = (K.index : ℂ) * ((Nat.card ↥K : ℂ) - 1) := by
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  have hbot : (⊥ : Subgroup L).subgroupOf K = ⊥ := by
    ext x; simp
  have h := OddOrder.Peterfalvi.S08.sum_div_normSq_induce_kernelFilter_eq (G := L) (H := K) (A := ⊥)
  have hfilter : (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
      (↑((⊥ : Subgroup L).subgroupOf K) : Set ↥K) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ) ∧
        θ ≠ trivialIrreducibleCharacter ↥K))
      = Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
        θ ≠ trivialIrreducibleCharacter ↥K) := by
    refine Finset.filter_congr fun θ _ => ?_
    rw [and_iff_right_iff_imp]
    intro _
    rw [hbot, Subgroup.coe_bot]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  rw [hfilter] at h
  rw [h, hbot]
  congr 2
  exact_mod_cast Nat.card_congr QuotientGroup.quotientBot.toEquiv

/-- **(1.5.d) family degree-sum** (reindexed to the distinct-induced enumeration).  For a
`DistinctInducedFamily` enumeration `θ` with `Ind 1_H` at `ind1H`, the family degree-sum over
`i ≠ ind1H` equals the `induce_degree_sum_bot` image sum `= [L:K]·(|K|−1)`.  The reindexing is
`Finset.sum_image` (injectivity `hinj`); the image equality uses `hcover` and the orbit fact
`Ind θ' = Ind 1_H ↔ θ' = 1` (via `⟨Ind θ', 1_L⟩ = 0` for `θ' ≠ 1` vs `⟨Ind 1_H, 1_L⟩ = 1`). -/
theorem family_degree_sum {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    (K : Subgroup L) [K.Normal] [Finite ↥K] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (ind1H : Fin (n + 1)) (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K) :
    ∑ i ∈ Finset.univ.erase ind1H,
        ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) 1 ^ 2 /
          ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) =
      (K.index : ℂ) * ((Nat.card ↥K : ℂ) - 1) := by
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  rw [← induce_degree_sum_bot K,
    ← Finset.sum_image (f := fun φ : ClassFunction L ℂ => φ 1 ^ 2 / ClassFunction.inner φ φ)
      (g := fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
      (fun i _ j _ h => hinj h)]
  congr 1
  ext φ
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter,
    true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨θ i, ?_, rfl⟩
    intro hc
    exact hi (hinj (show ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
      = ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ) by rw [hc, hzeta_ind1H]))
  · rintro ⟨φ', hφ', rfl⟩
    obtain ⟨j, hj⟩ := hcover φ'
    refine ⟨j, ?_, hj⟩
    intro hjeq
    have hone : ClassFunction.inner (ClassFunction.induce K (φ' : ClassFunction ↥K ℂ))
        (Hypothesis71.constOne L) = 1 := by
      rw [← hj, hjeq]
      change ClassFunction.inner (ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ))
        (Hypothesis71.constOne L) = 1
      rw [hzeta_ind1H]; exact inner_induce_trivialChar_constOne_eq_one K
    rw [inner_induce_constOne_eq_zero K φ' hφ'] at hone
    exact one_ne_zero hone.symm

/-- **(1.5.d) off-distinguished degree-sum** (`G`).  Removing the distinguished `ζ_0` (index `0`,
with `ζ_0(1) = [L:K]` and `‖ζ_0‖² = 1`) from `family_degree_sum` gives the `(7.8.b)` quantity
`G = Σ_{i ∈ Ioi 0, i ≠ ind1H} ζ_i(1)²/‖ζ_i‖² = [L:K]·(|K|−1) − [L:K]²` (`= e(h−1) − e²`). -/
theorem family_degree_sum_Ioi {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    (K : Subgroup L) [K.Normal] [Finite ↥K] [Invertible (Nat.card ↥K : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥K)
    (hinj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥K,
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
        Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
    (ind1H : Fin (n + 1)) (hind : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K)
    (hz0_deg : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) 1 = (K.index : ℂ))
    (hz0_norm : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) = 1) :
    ∑ i ∈ (Finset.Ioi (0 : Fin (n + 1))).erase ind1H,
        ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) 1 ^ 2 /
          ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
            (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)) =
      (K.index : ℂ) * ((Nat.card ↥K : ℂ) - 1) - (K.index : ℂ) ^ 2 := by
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  have hIoi : (Finset.Ioi (0 : Fin (n + 1))).erase ind1H
      = (Finset.univ.erase ind1H).erase 0 := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_Ioi, Finset.mem_univ, and_true, Fin.pos_iff_ne_zero]
    tauto
  have h0mem : (0 : Fin (n + 1)) ∈ Finset.univ.erase ind1H :=
    Finset.mem_erase.mpr ⟨Ne.symm hind, Finset.mem_univ _⟩
  rw [hIoi, Finset.sum_erase_eq_sub h0mem,
    family_degree_sum K θ hinj hcover ind1H hzeta_ind1H, hz0_deg, hz0_norm]
  ring

/-- **(7.8.b) ℂ-level norm identity at the `Hypothesis78` level** (the `h_inner` producer).  Lifts
`zetaNuRho_inner_eq_cexpr` (stated for `chiRhoCF (ν ζ_0)`) to
`H78.zetaNuRho = chiRhoCF (ν ζ_{zetaDistinct})` under the constructor convention `zetaDistinct = 0`,
then identifies the off-distinguished degree sum
`G = Σ_{i ∈ Ioi 0, i ≠ ind1H} ζ_i(1)²/‖ζ_i‖²` with `e·(h−1) − e²` (via `hGsum`, the `(1.5.d)`
`family_degree_sum_Ioi` value) and `|L| = e·h` (Lagrange
`kernelOrder_mul_complementIndex_eq_card_L`).
The conclusion is in the `(e_ℝ:ℂ)` real-cast shape consumed by `zetaNuRhoNormSq_eq_normQuad`. -/
theorem zetaNuRho_inner_eq_cexpr_H78 {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzd : H78.zetaDistinct = 0)
    (horth : ∀ i j : Fin (H78.hyp76.n + 1), i ≠ j →
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) = 0)
    (hc_ind1H : H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) H78.ind1H = (hBD.a : ℂ) - 1)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ H78.ind1H →
      H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) i = -(H78.hyp76.d i))
    (hd_real : ∀ i, star (H78.hyp76.d i) = H78.hyp76.d i)
    (hP_real : ∀ i, star (H78.hyp76.zeta i 1) = H78.hyp76.zeta i 1)
    (hd : ∀ i, H78.hyp76.d i = H78.hyp76.zeta i 1 / (H78.complementIndex : ℂ))
    (hN_ind1H : H78.hyp76.zetaNormSq H78.ind1H = (H78.complementIndex : ℂ))
    (hP_ind1H : H78.hyp76.zeta H78.ind1H 1 = (H78.complementIndex : ℂ))
    (hGsum : ∑ i ∈ (Finset.Ioi (0 : Fin (H78.hyp76.n + 1))).erase H78.ind1H,
        H78.hyp76.zeta i 1 ^ 2 / H78.hyp76.zetaNormSq i
      = (H78.complementIndex : ℂ) * ((H78.kernelOrder : ℂ) - 1) - (H78.complementIndex : ℂ) ^ 2) :
    ClassFunction.inner H78.zetaNuRho H78.zetaNuRho =
      (((hBD.a : ℝ) : ℂ) - 1) ^ 2 / ((H78.complementIndex : ℝ) : ℂ)
        + (((H78.complementIndex : ℝ) * ((H78.kernelOrder : ℝ) - 1)
              - (H78.complementIndex : ℝ) ^ 2 : ℝ) : ℂ) / ((H78.complementIndex : ℝ) : ℂ) ^ 2
        - ((((hBD.a : ℝ) : ℂ) - 1)
            - (((H78.complementIndex : ℝ) * ((H78.kernelOrder : ℝ) - 1)
                  - (H78.complementIndex : ℝ) ^ 2 : ℝ) : ℂ) / ((H78.complementIndex : ℝ) : ℂ)) ^ 2
          / (((H78.complementIndex : ℝ) : ℂ) * ((H78.kernelOrder : ℝ) : ℂ)) := by
  have he_ne : (H78.complementIndex : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr H78.complementIndex_pos.ne'
  have hind : H78.ind1H ≠ 0 := fun h => H78.zetaDistinct_ne_ind1H (hzd.trans h.symm)
  have ha1_real : star ((hBD.a : ℂ) - 1) = (hBD.a : ℂ) - 1 := by simp
  have hLcard : (Nat.card L : ℂ) = (H78.complementIndex : ℂ) * (H78.kernelOrder : ℂ) := by
    rw [mul_comm]; exact_mod_cast H78.kernelOrder_mul_complementIndex_eq_card_L.symm
  simp only [OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRho, hzd]
  rw [zetaNuRho_inner_eq_cexpr H78.hyp76 H78.nu (hBD.a : ℂ) (H78.complementIndex : ℂ) hind horth
      hc_ind1H hc_rest ha1_real hd_real hP_real hd hN_ind1H hP_ind1H he_ne,
    hGsum, hLcard]
  push_cast
  ring

/-- **Peterfalvi (7.8.b), the `ζ`-norm lower bound** (`Hypothesis78` level).  Assembles the full
chain: the `h_inner` identity `zetaNuRho_inner_eq_cexpr_H78`, the real-part identification
`zetaNuRhoNormSq_eq_normQuad` (`‖ζ_0^{νρ}‖² = normQuadraticCorrection + (1 − e/h)`), and the
nonnegativity reduction `zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq` (valid under
`2e + 1 ≤ h`).  The result `1 − e/h ≤ ‖ζ_0^{νρ}‖²` is exactly the (7.8.b)
`NormEstimates.zetaNuRho_norm_sq_ge` target, discharged from the abstract
`(7.8.a)`-decomposition / coherence / degree facts. -/
theorem zetaNuRhoNormSq_eq_normQuad_of_facts {G : Type*} [Group G] [Fintype G] {A : Set G}
    {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzd : H78.zetaDistinct = 0)
    (horth : ∀ i j : Fin (H78.hyp76.n + 1), i ≠ j →
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) = 0)
    (hc_ind1H : H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) H78.ind1H = (hBD.a : ℂ) - 1)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ H78.ind1H →
      H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) i = -(H78.hyp76.d i))
    (hd_real : ∀ i, star (H78.hyp76.d i) = H78.hyp76.d i)
    (hP_real : ∀ i, star (H78.hyp76.zeta i 1) = H78.hyp76.zeta i 1)
    (hd : ∀ i, H78.hyp76.d i = H78.hyp76.zeta i 1 / (H78.complementIndex : ℂ))
    (hN_ind1H : H78.hyp76.zetaNormSq H78.ind1H = (H78.complementIndex : ℂ))
    (hP_ind1H : H78.hyp76.zeta H78.ind1H 1 = (H78.complementIndex : ℂ))
    (hGsum : ∑ i ∈ (Finset.Ioi (0 : Fin (H78.hyp76.n + 1))).erase H78.ind1H,
        H78.hyp76.zeta i 1 ^ 2 / H78.hyp76.zetaNormSq i
      = (H78.complementIndex : ℂ) * ((H78.kernelOrder : ℂ) - 1) - (H78.complementIndex : ℂ) ^ 2) :
    H78.zetaNuRhoNormSq =
      H78.normQuadraticCorrection hBD
        + (1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)) :=
  zetaNuRhoNormSq_eq_normQuad H78 hBD (hBD.a : ℝ) (H78.complementIndex : ℝ) (H78.kernelOrder : ℝ)
    ((H78.complementIndex : ℝ) * ((H78.kernelOrder : ℝ) - 1) - (H78.complementIndex : ℝ) ^ 2)
    (Nat.cast_ne_zero.mpr H78.complementIndex_pos.ne')
    (Nat.cast_ne_zero.mpr H78.kernelOrder_pos.ne') rfl rfl rfl rfl
    (zetaNuRho_inner_eq_cexpr_H78 H78 hBD hzd horth hc_ind1H hc_rest hd_real hP_real hd
      hN_ind1H hP_ind1H hGsum)

/-- **Peterfalvi (7.8.b), the `ζ`-norm lower bound** (`Hypothesis78` level).  The direct `≤` form of
the (7.8.b) target `NormEstimates.zetaNuRho_norm_sq_ge`: from the
`zetaNuRhoNormSq_eq_normQuad_of_facts`
identity and the `smallIndex` (`2e + 1 ≤ h`) nonnegativity reduction
`zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq`, the coherent `ζ`-image satisfies
`1 − e/h ≤ ‖ζ_0^{νρ}‖²`.

To obtain the *full* (7.8.b) `NormEstimates` (both the `ζ` bound and the `Γ` bound `‖Γ‖² ≤ e − 1`),
feed `zetaNuRhoNormSq_eq_normQuad_of_facts` as the `hzeta` argument of the already-assembled
source-side
`OddOrder.Peterfalvi.S09.Hypothesis78.normEstimates_of_source_orthogonal`. -/
theorem zetaNuRhoNormSq_ge_of_facts {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hzd : H78.zetaDistinct = 0)
    (horth : ∀ i j : Fin (H78.hyp76.n + 1), i ≠ j →
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) = 0)
    (hc_ind1H : H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) H78.ind1H = (hBD.a : ℂ) - 1)
    (hc_rest : ∀ i, i ≠ 0 → i ≠ H78.ind1H →
      H78.hyp76.cCoeff (H78.nu (H78.hyp76.zeta 0)) i = -(H78.hyp76.d i))
    (hd_real : ∀ i, star (H78.hyp76.d i) = H78.hyp76.d i)
    (hP_real : ∀ i, star (H78.hyp76.zeta i 1) = H78.hyp76.zeta i 1)
    (hd : ∀ i, H78.hyp76.d i = H78.hyp76.zeta i 1 / (H78.complementIndex : ℂ))
    (hN_ind1H : H78.hyp76.zetaNormSq H78.ind1H = (H78.complementIndex : ℂ))
    (hP_ind1H : H78.hyp76.zeta H78.ind1H 1 = (H78.complementIndex : ℂ))
    (hGsum : ∑ i ∈ (Finset.Ioi (0 : Fin (H78.hyp76.n + 1))).erase H78.ind1H,
        H78.hyp76.zeta i 1 ^ 2 / H78.hyp76.zetaNormSq i
      = (H78.complementIndex : ℂ) * ((H78.kernelOrder : ℂ) - 1) - (H78.complementIndex : ℂ) ^ 2)
    (hsmall : H78.smallIndex) :
    1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤ H78.zetaNuRhoNormSq :=
  H78.zetaNuRhoNormSq_ge_of_normQuadraticCorrection_eq hBD
    (zetaNuRhoNormSq_eq_normQuad_of_facts H78 hBD hzd horth hc_ind1H hc_rest hd_real hP_real hd
      hN_ind1H hP_ind1H hGsum) hsmall

/-- **Peterfalvi (7.8.a), the `BetaDecomp` constructor** (`Hypothesis78` level).  Assembles the full
`(7.8.a)` decomposition `β = 1_G − ζ_0^ν + a · W + Γ` (with `Γ` the explicit residual) for an
abstract `H78` from the `(7.8.a)` coherence / family facts, discharging all four `BetaDecomp` proof
fields via the family-agnostic gen lemmas (`betaDecomp_orth_one_gen`,
`betaDecomp_gamma_orth_nu_gen`,
`betaDecomp_gamma_orth_one_gen`).  Because `H78` is abstract here (not a `hypothesis78OfDade`
application), the field projections `H78.hyp76.zeta` / `H78.beta` / `H78.weightedNuSum` do not trip
the whnf-wall.  The hypotheses (family orthogonality, coherence agreement `hagree`, source
orthogonalities, `⟨β,1_G⟩ = 1`, `‖ζ_0‖² = 1`, the integer `a`) are all constructible from the Dade
family; `a` is `exists_betaDecomp_a`. -/
noncomputable def betaDecompOfFacts {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hzd : H78.zetaDistinct = 0)
    (horth : ∀ i j : Fin (H78.hyp76.n + 1), i ≠ j →
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) = 0)
    (hN : ∀ j : Fin (H78.hyp76.n + 1),
      ClassFunction.inner (H78.hyp76.zeta j) (H78.hyp76.zeta j) ≠ 0)
    (hz0 : H78.hyp76.zeta 0 (1 : ↥L) ≠ 0)
    (hP_real : ∀ i, star (H78.hyp76.zeta i (1 : ↥L)) = H78.hyp76.zeta i (1 : ↥L))
    (hagree : ∀ i : Fin (H78.hyp76.n + 1), i ≠ 0 → i ≠ H78.ind1H →
      H78.hyp76.hyp71.τ ⟨H78.hyp76.zeta i - H78.hyp76.d i • H78.hyp76.zeta 0,
          H78.hyp76.psi_support i⟩
        = H78.nu (H78.hyp76.zeta i) - H78.hyp76.d i • H78.nu (H78.hyp76.zeta 0))
    (hzeta0nu : ClassFunction.inner (H78.nu (H78.hyp76.zeta 0)) (Hypothesis71.constOne G) = 0)
    (hzeta_orth_one : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.hyp76.zeta i) (Hypothesis71.constOne L) = 0)
    (hβ1 : ClassFunction.inner H78.beta (Hypothesis71.constOne G) = 1)
    (hζ0norm : ClassFunction.inner (H78.hyp76.zeta 0) (H78.hyp76.zeta 0) = 1)
    (a : ℤ) (ha : (a : ℂ) = ClassFunction.inner H78.beta (H78.nu (H78.hyp76.zeta 0)) + 1) :
    H78.BetaDecomp := by
  have hind0 : H78.ind1H ≠ 0 := fun h => H78.zetaDistinct_ne_ind1H (hzd.trans h.symm)
  have hd : ∀ i, H78.hyp76.d i = H78.hyp76.zeta i (1 : ↥L) / H78.hyp76.zeta 0 (1 : ↥L) :=
    fun i => by rw [eq_div_iff hz0]; exact (H78.hyp76.zeta_one_eq_d_mul i).symm
  have diffβ : (H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta 0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    have h := H78.diff_support; rw [hzd] at h; exact h
  have hβ : H78.beta
      = H78.hyp76.hyp71.τ ⟨H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta 0, diffβ⟩ := by
    rw [H78.beta_def]; congr 1; apply Subtype.ext
    change H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct
      = H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta 0
    rw [hzd]
  have hW : H78.weightedNuSum = ∑ i ∈ Finset.univ.erase H78.ind1H,
      (H78.hyp76.zeta i (1 : ↥L) /
        (H78.hyp76.zeta 0 (1 : ↥L) * ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))
        : ℂ) • H78.nu (H78.hyp76.zeta i) := by
    unfold OddOrder.Peterfalvi.S09.Hypothesis78.weightedNuSum; rw [hzd]
  have horth1 : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner (H78.nu (H78.hyp76.zeta i)) (Hypothesis71.constOne G) = 0 :=
    betaDecomp_orth_one_gen H78.hyp76.hyp71 H78.hyp76.zeta H78.hyp76.d H78.hyp76.psi_support
      H78.ind1H hind0 H78.nu hagree hzeta0nu hzeta_orth_one
  exact
    { orth_one := horth1
      a := a
      Gamma := H78.beta - (Hypothesis71.constOne G - H78.nu (H78.hyp76.zeta 0)
        + (a : ℂ) • H78.weightedNuSum)
      Gamma_orth_nu := fun i hi =>
        betaDecomp_gamma_orth_nu_gen H78.hyp76.hyp71 H78.hyp76.isDadeIsometry H78.hyp76.zeta
          horth hN hz0 hP_real H78.hyp76.d hd H78.hyp76.psi_support hind0 diffβ H78.nu
          H78.nu_isometry (fun i hi0 hii => (hagree i hi0 hii).symm) horth1 hζ0norm H78.beta hβ
          (a : ℂ) ha H78.weightedNuSum hW hi
      Gamma_orth_one :=
        betaDecomp_gamma_orth_one_gen H78.hyp76.zeta hind0 H78.nu horth1 H78.beta hβ1
          (a : ℂ) H78.weightedNuSum hW
      beta_eq := by rw [hzd]; abel }

/-- **Peterfalvi (7.8.a), the concrete `BetaDecomp` over a Dade family** (`hypothesis78OfDade`).
Bundles `hypothesis78OfDade` with `betaDecompOfFacts`: for the concrete `H78` built from a Dade
family `θ`, every `betaDecompOfFacts` fact is discharged from the induced-family lemmas
(`induce_family_orthogonal_of_injective` / `induce_norm_ne_zero` / `induce_apply_one_ne_zero` /
`induce_apply_one_star` / `inner_induce_constOne_eq_zero`), with the `d`-coefficient identification
`H78.hyp76.d = ζ_i(1)/ζ_0(1)` bridging the constructor's computed `d` to the supplied `hdeg`.  The
field projections `.hyp76.zeta` / `.nu` / `.hyp76.hyp71` / `.hyp76.d` all reduce by `rfl` (no
whnf-wall), so the discharge is purely the induced-character source facts.  The remaining genuine
`(7.8.a)` coherence inputs are `hzeta0nu` (`ζ_0^ν ⊥ 1_G`), `hζ0norm` (`‖ζ_0‖² = 1`), and the
integer `a` of `(7.8.a)`. -/
noncomputable def betaDecompOfDade
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    [Fintype ↥(H.subgroupOf L)] [Invertible (Nat.card ↥(H.subgroupOf L) : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥(H.subgroupOf L))
    (hinj : Function.Injective
      (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ) ∈
        Set.range (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
        - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdeg : ∀ i, ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
        = d i * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥(H.subgroupOf L))
    (hdeg_match : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) (1 : ↥L))
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
          (ν (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          - d i • ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)))
    (hzeta0nu : ClassFunction.inner (ν (ClassFunction.induce (H.subgroupOf L)
        (θ 0 : ClassFunction _ ℂ))) (Hypothesis71.constOne G) = 0)
    (hζ0norm : ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))
      (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)) = 1)
    (a : ℤ) (ha : (a : ℂ) = ClassFunction.inner
      (hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H
        hzeta_ind1H hdeg_match ν hnu_isometry hagree).beta
      (ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))) + 1) :
    (hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H
        hzeta_ind1H hdeg_match ν hnu_isometry hagree).BetaDecomp := by
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  set H78 := hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H
    hind1H hzeta_ind1H hdeg_match ν hnu_isometry hagree with hH78
  have hz0 : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (θ 0)
  -- `θ_i ≠ 1_K` for `i ≠ ind1H` (injectivity + `θ_{ind1H} = 1_K`).
  have hne_triv : ∀ j : Fin (n + 1), j ≠ ind1H → θ j ≠ trivialIrreducibleCharacter ↥(H.subgroupOf
      L) :=
    fun j hj hc => hj (hinj (by
      change ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)
        = ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ)
      rw [hc, hzeta_ind1H]))
  -- The constructor's computed `d` agrees with the supplied `d` (both `= ζ_i(1)/ζ_0(1)`).
  have hdeq : ∀ i, H78.hyp76.d i = d i := fun i => by
    change ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) = d i
    rw [div_eq_iff hz0]; exact hdeg i
  -- Coherence agreement transported from the supplied `d` to the constructor's computed `d`
  -- (equal by `hdeq`); the `SupportedClassFunctions` subtype is fixed by `Subtype.ext`.
  have hagree' : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ H78.ind1H →
      H78.hyp76.hyp71.τ ⟨H78.hyp76.zeta i - H78.hyp76.d i • H78.hyp76.zeta 0,
          H78.hyp76.psi_support i⟩
        = H78.nu (H78.hyp76.zeta i) - H78.hyp76.d i • H78.nu (H78.hyp76.zeta 0) := by
    intro i hi0 hii
    have hsub : (⟨H78.hyp76.zeta i - H78.hyp76.d i • H78.hyp76.zeta 0, H78.hyp76.psi_support i⟩ :
        OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L)
        = ⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
            - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ),
          psi_support i⟩ := by
      apply Subtype.ext
      change ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - H78.hyp76.d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)
        = ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)
      rw [hdeq i]
    rw [hsub, hdeq i]
    exact hagree i hi0 hii
  -- `⟨β, 1_G⟩ = ⟨Ind 1_K − ζ_0, 1_L⟩ = 1 − 0 = 1`.
  have hz_ind : H78.hyp76.zeta H78.ind1H = ClassFunction.induce (H.subgroupOf L)
      (trivialIrreducibleCharacter ↥(H.subgroupOf L) : ClassFunction _ ℂ) := by
    change ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) = _
    rw [hzeta_ind1H]
  have hz_zd : H78.hyp76.zeta H78.zetaDistinct
      = ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) := rfl
  have hβ1 : ClassFunction.inner H78.beta (Hypothesis71.constOne G) = 1 := by
    rw [H78.beta_def, inner_tau_supported_constOne, ClassFunction.inner_sub_left, hz_ind, hz_zd,
      inner_induce_trivialChar_constOne_eq_one,
      inner_induce_constOne_eq_zero (H.subgroupOf L) (θ 0) (hne_triv 0 (Ne.symm hind1H)), sub_zero]
  exact betaDecompOfFacts H78 rfl
    (induce_family_orthogonal_of_injective (H.subgroupOf L) θ hinj)
    (fun j => induce_norm_ne_zero (H.subgroupOf L) (θ j)) hz0
    (fun i => induce_apply_one_star (H.subgroupOf L) (θ i))
    hagree' hzeta0nu
    (fun i hi => inner_induce_constOne_eq_zero (H.subgroupOf L) (θ i) (hne_triv i hi))
    hβ1 hζ0norm a ha

/-- **`e = [L : H◁L]`**, the complement index as the `subgroupOf` index.  By Lagrange both equal
`|L| / |H|`: `(H.subgroupOf L).index · |H.subgroupOf L| = |L|` and `|H.subgroupOf L| = |H|`, while
`e · |H| = |L|` (`kernelOrder_mul_complementIndex_eq_card_L`); cancelling `|H| > 0` identifies them.
This bridges the induced-principal degree/norm `‖Ind 1_K‖² = Ind 1_K(1) = [L:K]`
(`K = H.subgroupOf L`)
to the `(7.8.b)` complement index `e`, the `hN_ind1H`/`hP_ind1H` source facts. -/
theorem complementIndex_eq_subgroupOf_index {G : Type*} [Group G] [Fintype G] {A : Set G}
    {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) :
    H78.complementIndex = (H78.hyp76.H.subgroupOf L).index := by
  have hKcard : Nat.card ↥(H78.hyp76.H.subgroupOf L) = Nat.card H78.hyp76.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe H78.hyp76.H_le_L).toEquiv
  have hpos : 0 < Nat.card H78.hyp76.H := Nat.card_pos
  have h1 : (H78.hyp76.H.subgroupOf L).index * Nat.card H78.hyp76.H = Nat.card L := by
    rw [← hKcard, Subgroup.index_mul_card]
  have h2 : Nat.card H78.hyp76.H * H78.complementIndex = Nat.card L :=
    H78.kernelOrder_mul_complementIndex_eq_card_L
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h2, mul_comm, h1]

/-- **Peterfalvi (7.8.b), the concrete ζ-norm bound over a Dade family** (the `hB` producer).
Bundles `hypothesis78OfDade` + `betaDecompOfDade` with the (7.8.b) ζ-bound
`zetaNuRhoNormSq_ge_of_facts`:
for the concrete `H78` from a Dade family `θ`, the `(7.8.b)` facts are discharged — coefficient
identifications `c_{ind1H} = a−1` / `c_i = −d_i` (`cCoeff_nu_zeta_zero_ind1H_eq` /
`cCoeff_nu_zeta_zero_eq_neg_d`, with the `hagree` transported to computed-`d`/`psiSupp` form),
reality (`induce_apply_one_star`), degree ratio `d_i = ζ_i(1)/e` (via `zeta_one_eq_ind1H_one`
giving `ζ_0(1) = ζ_{ind1H}(1) = e`), the index facts `‖Ind 1_K‖² = Ind 1_K(1) = e`
(`induce_trivialChar_*_eq_index` + `complementIndex_eq_subgroupOf_index`), and the `(1.5.d)`
degree-sum (`family_degree_sum_Ioi`). Yields `1 − e/h ≤ ‖ζ_0^{νρ}‖²`, the
`CounterexampleDadeData.hB`
contract of (12.16). Genuine `(7.8.b)` inputs: `hzeta0nu`/`hζ0norm`/`a`/`ha` (as in
`betaDecompOfDade`)
and the smallness `hsmall`. -/
theorem zetaNuRhoNormSqGeOfDade
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    [Fintype ↥(H.subgroupOf L)] [Invertible (Nat.card ↥(H.subgroupOf L) : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥(H.subgroupOf L))
    (hinj : Function.Injective
      (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ) ∈
        Set.range (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
        - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdeg : ∀ i, ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
        = d i * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥(H.subgroupOf L))
    (hdeg_match : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) (1 : ↥L))
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
          (ν (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          - d i • ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)))
    (hzeta0nu : ClassFunction.inner (ν (ClassFunction.induce (H.subgroupOf L)
        (θ 0 : ClassFunction _ ℂ))) (Hypothesis71.constOne G) = 0)
    (hζ0norm : ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))
      (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)) = 1)
    (a : ℤ) (ha : (a : ℂ) = ClassFunction.inner
      (hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H
        hzeta_ind1H hdeg_match ν hnu_isometry hagree).beta
      (ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))) + 1)
    (hsmall : (hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H
        hind1H hzeta_ind1H hdeg_match ν hnu_isometry hagree).smallIndex) :
    1 - ((hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H
            hzeta_ind1H hdeg_match ν hnu_isometry hagree).complementIndex : ℝ)
        / ((hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H
            hzeta_ind1H hdeg_match ν hnu_isometry hagree).kernelOrder : ℝ)
      ≤ (hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H
          hzeta_ind1H hdeg_match ν hnu_isometry hagree).zetaNuRhoNormSq := by
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  set H78 := hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H
    hind1H hzeta_ind1H hdeg_match ν hnu_isometry hagree with hH78
  set hBD := betaDecompOfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H
    hind1H hzeta_ind1H hdeg_match ν hnu_isometry hagree hzeta0nu hζ0norm a ha with hBDdef
  have hBDa : hBD.a = a := rfl
  have hz0 : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (θ 0)
  have hne_triv : ∀ j : Fin (n + 1), j ≠ ind1H → θ j ≠ trivialIrreducibleCharacter ↥(H.subgroupOf
      L) :=
    fun j hj hc => hj (hinj (by
      change ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)
        = ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ)
      rw [hc, hzeta_ind1H]))
  have hdeq : ∀ i, H78.hyp76.d i = d i := fun i => by
    change ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) = d i
    rw [div_eq_iff hz0]; exact hdeg i
  have hagree' : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ H78.ind1H →
      H78.hyp76.hyp71.τ (H78.hyp76.psiSupp i)
        = H78.nu (H78.hyp76.zeta i) - H78.hyp76.d i • H78.nu (H78.hyp76.zeta 0) := by
    intro i hi0 hii
    have hsub : H78.hyp76.psiSupp i
        = (⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
            - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ),
          psi_support i⟩ : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L) := by
      apply Subtype.ext
      change ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - H78.hyp76.d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)
        = ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)
      rw [hdeq i]
    rw [hsub, hdeq i]
    exact hagree i hi0 hii
  have hz_ind : H78.hyp76.zeta H78.ind1H = ClassFunction.induce (H.subgroupOf L)
      (trivialIrreducibleCharacter ↥(H.subgroupOf L) : ClassFunction _ ℂ) := by
    change ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) = _
    rw [hzeta_ind1H]
  have hd1 : H78.hyp76.d H78.ind1H = 1 := by
    change ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) = 1
    rw [← hdeg_match, div_self hz0]
  have hP_ind1H : H78.hyp76.zeta H78.ind1H (1 : ↥L) = (H78.complementIndex : ℂ) := by
    rw [complementIndex_eq_subgroupOf_index H78, hz_ind]
    exact induce_trivialChar_apply_eq_index (H.subgroupOf L) (Subgroup.one_mem _)
  have hN_ind1H : H78.hyp76.zetaNormSq H78.ind1H = (H78.complementIndex : ℂ) := by
    rw [complementIndex_eq_subgroupOf_index H78]
    change ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H)
      = ((H78.hyp76.H.subgroupOf L).index : ℂ)
    rw [hz_ind]
    exact induce_trivialChar_normSq_eq_index (H.subgroupOf L)
  have hz0_compl : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
      = (H78.complementIndex : ℂ) := by
    change H78.hyp76.zeta H78.zetaDistinct (1 : ↥L) = (H78.complementIndex : ℂ)
    rw [H78.zeta_one_eq_ind1H_one, hP_ind1H]
  have hz0_deg : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
      = ((H.subgroupOf L).index : ℂ) := by
    rw [hz0_compl]; exact_mod_cast complementIndex_eq_subgroupOf_index H78
  have hGsum : ∑ i ∈ (Finset.Ioi (0 : Fin (H78.hyp76.n + 1))).erase H78.ind1H,
        H78.hyp76.zeta i 1 ^ 2 / H78.hyp76.zetaNormSq i
      = (H78.complementIndex : ℂ) * ((H78.kernelOrder : ℂ) - 1) - (H78.complementIndex : ℂ) ^ 2 :=
          by
    rw [complementIndex_eq_subgroupOf_index H78,
      show (H78.kernelOrder : ℂ) = (Nat.card ↥(H.subgroupOf L) : ℂ) from by
        rw [show H78.kernelOrder = Nat.card ↥(H.subgroupOf L) from
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv).symm]]
    exact family_degree_sum_Ioi (H.subgroupOf L) θ hinj hcover ind1H hind1H hzeta_ind1H hz0_deg
        hζ0norm
  exact zetaNuRhoNormSq_ge_of_facts H78 hBD rfl
    (induce_family_orthogonal_of_injective (H.subgroupOf L) θ hinj)
    (by
      rw [cCoeff_nu_zeta_zero_ind1H_eq H78 H78.nu rfl hd1, hBDa]
      change ClassFunction.inner H78.beta
        (ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))) = (a : ℂ) - 1
      rw [ha]; ring)
    (fun i hi0 hii => cCoeff_nu_zeta_zero_eq_neg_d H78.hyp76 H78.nu hagree' H78.nu_isometry
      (Ne.symm hind1H)
      (fun i hi => induce_family_orthogonal_of_injective (H.subgroupOf L) θ hinj i 0 hi)
      hζ0norm i hi0 hii)
    (fun i => by
      change star (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L) /
          ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
        = ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L) /
          ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
      rw [star_div₀, induce_apply_one_star, induce_apply_one_star])
    (fun i => induce_apply_one_star (H.subgroupOf L) (θ i))
    (fun i => by
      change ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L) /
          ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
          / (H78.complementIndex : ℂ)
      rw [hz0_compl])
    hN_ind1H hP_ind1H hGsum hsmall

/-- **Peterfalvi (12.14), the `a = 0` step.**  The (7.8.a) coefficient `a` of a `BetaDecomp`
vanishes under the witness numerics.  From `‖β‖² = e + 1`
(`betaNormSq_eq_complementIndex_add_one`) and its orthogonal expansion
`‖β‖² = 2 + ((h−1)/e)·a² − 2a + ‖Γ‖²` (`betaNormSq_eq_of_source_orthogonal`) with `‖Γ‖² ≥ 0`,
the integer `a` satisfies `((h−1)/e)·a² − 2a ≤ e − 1`; with `p² ≤ h` (the rank-two `P₀ ⊆ H`)
and `2e ≤ p + 1` (Peterfalvi (12.12)) this gives `2(p−1)·a² − 2a ≤ (p−1)/2`, which for `p ≥ 3`
forces `a = 0`: `a ≥ 1` makes the left side at least `2p − 4 > (p−1)/2`, and `a ≤ −1` makes it
at least `2p > (p−1)/2`. -/
theorem betaDecomp_a_eq_zero_of_p_bounds {G : Type*} [Group G] [Fintype G] {A : Set G}
    {L : Subgroup G} [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G A L) (hBD : H78.BetaDecomp)
    (hbetaNorm : H78.betaNormSq = (H78.complementIndex : ℝ) + 1)
    (hexpand : H78.betaNormSq =
      2 + (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) * (hBD.a : ℝ) ^ 2
        - 2 * (hBD.a : ℝ) + H78.gammaNormSq hBD)
    {p : ℕ} (hp3 : 3 ≤ p)
    (hph : (p : ℝ) ^ 2 ≤ (H78.kernelOrder : ℝ))
    (h2e : 2 * (H78.complementIndex : ℝ) ≤ (p : ℝ) + 1) :
    hBD.a = 0 := by
  have hgamma_nonneg : 0 ≤ H78.gammaNormSq hBD :=
    OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_self_re_nonneg hBD.Gamma
  have he_pos : (0 : ℝ) < (H78.complementIndex : ℝ) := by
    exact_mod_cast H78.complementIndex_pos
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  -- `((h−1)/e)·a² − 2a ≤ e − 1`.
  have hkey : (((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ)) * (hBD.a : ℝ) ^ 2
      - 2 * (hBD.a : ℝ) ≤ (H78.complementIndex : ℝ) - 1 := by
    have h := hexpand.symm.trans hbetaNorm
    linarith
  -- `2(p−1) ≤ (h−1)/e`: from `h ≥ p²` and `2e ≤ p + 1`.
  have hfrac : 2 * ((p : ℝ) - 1) ≤ ((H78.kernelOrder : ℝ) - 1) / (H78.complementIndex : ℝ) := by
    rw [le_div_iff₀ he_pos]
    nlinarith
  have hL : 2 * ((p : ℝ) - 1) * (hBD.a : ℝ) ^ 2 - 2 * (hBD.a : ℝ)
      ≤ (H78.complementIndex : ℝ) - 1 := by
    have hmul := mul_le_mul_of_nonneg_right hfrac (sq_nonneg ((hBD.a : ℝ)))
    linarith
  have he_ub : (H78.complementIndex : ℝ) - 1 ≤ ((p : ℝ) - 1) / 2 := by linarith
  rcases lt_trichotomy hBD.a 0 with hneg | hzero | hpos
  · exfalso
    have ha1 : (hBD.a : ℝ) ≤ -1 := by
      have h1 : hBD.a ≤ -1 := by omega
      exact_mod_cast h1
    nlinarith [sq_nonneg ((hBD.a : ℝ) + 1)]
  · exact hzero
  · exfalso
    have ha1 : (1 : ℝ) ≤ (hBD.a : ℝ) := by exact_mod_cast hpos
    nlinarith [sq_nonneg ((hBD.a : ℝ) - 1)]

open OddOrder.Peterfalvi.S09 in
/-- **Peterfalvi (12.14), `a = 0` for the Dade-realized family.**  In the setting of
`zetaNuRhoNormSqGeOfDade` (the `hypothesis78OfDade`/`betaDecompOfDade` realization of the (7.8)
machinery over a Dade isometry), the (7.8.a) coefficient `a = (β, ζ_0^ν) + 1` **vanishes** under
the (12.14) numerics: `ζ_0` irreducible, `p² ≤ |H|` (the rank-two `P₀ ⊆ H` of (12.9)),
`2·[L:H] ≤ p + 1` ((12.12)), `p ≥ 3` odd.  Discharges `‖β‖² = e + 1`
(`SourceDiffNormEvaluation` from the family inner values) and the orthogonal expansion
(`betaNormSq_eq_of_source_orthogonal`), then applies the arithmetic core
`betaDecomp_a_eq_zero_of_p_bounds`.  This is the counting step of Peterfalvi (12.14): with it the
(7.7.a) coefficients of `ψ = ζ_0^ν` collapse to `c_{ind1H} = −1`, `c_i = −d_i`. -/
theorem betaDecompOfDade_a_eq_zero
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    [Fintype ↥(H.subgroupOf L)] [Invertible (Nat.card ↥(H.subgroupOf L) : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥(H.subgroupOf L))
    (hinj : Function.Injective
      (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ) ∈
        Set.range (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
        - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdeg : ∀ i, ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
        = d i * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥(H.subgroupOf L))
    (hdeg_match : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) (1 : ↥L))
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
          (ν (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          - d i • ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)))
    (hzeta0nu : ClassFunction.inner (ν (ClassFunction.induce (H.subgroupOf L)
        (θ 0 : ClassFunction _ ℂ))) (Hypothesis71.constOne G) = 0)
    (hζ0norm : ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))
      (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)) = 1)
    (a : ℤ) (ha : (a : ℂ) = ClassFunction.inner
      (hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H
        hzeta_ind1H hdeg_match ν hnu_isometry hagree).beta
      (ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))) + 1)
    (hzeta_irr : IsIrreducibleCharacter
      (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)))
    {p : ℕ} (hp3 : 3 ≤ p)
    (hph : (p : ℝ) ^ 2 ≤ (Nat.card ↥H : ℝ))
    (h2e : 2 * (((H.subgroupOf L).index : ℝ)) ≤ (p : ℝ) + 1) :
    a = 0 := by
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  set H78 := hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H
    hind1H hzeta_ind1H hdeg_match ν hnu_isometry hagree with hH78
  set hBD := betaDecompOfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H
    hind1H hzeta_ind1H hdeg_match ν hnu_isometry hagree hzeta0nu hζ0norm a ha with hBDdef
  have hBDa : hBD.a = a := rfl
  have hz0 : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (θ 0)
  have hz_ind : H78.hyp76.zeta H78.ind1H = ClassFunction.induce (H.subgroupOf L)
      (trivialIrreducibleCharacter ↥(H.subgroupOf L) : ClassFunction _ ℂ) := by
    change ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) = _
    rw [hzeta_ind1H]
  have hP_ind1H : H78.hyp76.zeta H78.ind1H (1 : ↥L) = (H78.complementIndex : ℂ) := by
    rw [complementIndex_eq_subgroupOf_index H78, hz_ind]
    exact induce_trivialChar_apply_eq_index (H.subgroupOf L) (Subgroup.one_mem _)
  have hN_ind1H : H78.hyp76.zetaNormSq H78.ind1H = (H78.complementIndex : ℂ) := by
    rw [complementIndex_eq_subgroupOf_index H78]
    change ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H)
      = ((H78.hyp76.H.subgroupOf L).index : ℂ)
    rw [hz_ind]
    exact induce_trivialChar_normSq_eq_index (H.subgroupOf L)
  have hz0_compl : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
      = (H78.complementIndex : ℂ) := by
    change H78.hyp76.zeta H78.zetaDistinct (1 : ↥L) = (H78.complementIndex : ℂ)
    rw [H78.zeta_one_eq_ind1H_one, hP_ind1H]
  -- Family orthogonality in the `if`-diagonal form.
  have horth_if : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ∀ j ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) =
          if i = j then ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) else 0 := by
    intro i _ j _
    by_cases hij : i = j
    · rw [if_pos hij, hij]
    · rw [if_neg hij]
      exact induce_family_orthogonal_of_injective (H.subgroupOf L) θ hinj i j hij
  have hnorm_ne : ∀ i ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0 :=
    fun i _ => induce_norm_ne_zero (H.subgroupOf L) (θ i)
  -- Degree sum over `univ.erase ind1H`, with `star` collapsed by realness of degrees.
  have hdeg_sum : (∑ i ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
          ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i)) =
      ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ) := by
    have hstar : ∀ i : Fin (n + 1), star (H78.hyp76.zeta i (1 : L)) = H78.hyp76.zeta i (1 : L) :=
      fun i => induce_apply_one_star (H.subgroupOf L) (θ i)
    have hsq : ∀ i : Fin (n + 1),
        H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) =
          H78.hyp76.zeta i (1 : L) ^ 2 := fun i => by rw [hstar i, sq]
    calc (∑ i ∈ (Finset.univ.erase H78.ind1H),
          H78.hyp76.zeta i (1 : L) * star (H78.hyp76.zeta i (1 : L)) /
            ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i))
        = ∑ i ∈ (Finset.univ.erase H78.ind1H),
            H78.hyp76.zeta i (1 : L) ^ 2 /
              ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) :=
          Finset.sum_congr rfl fun i _ => by rw [hsq i]
      _ = ((H.subgroupOf L).index : ℂ) * ((Nat.card ↥(H.subgroupOf L) : ℂ) - 1) :=
          family_degree_sum (H.subgroupOf L) θ hinj hcover ind1H hzeta_ind1H
      _ = ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ) := by
          have hke : (H78.kernelOrder : ℂ) = (Nat.card ↥(H.subgroupOf L) : ℂ) := by
            exact_mod_cast congrArg (Nat.cast (R := ℂ))
              ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv).symm :
                H78.kernelOrder = Nat.card ↥(H.subgroupOf L))
          have hce : (H78.complementIndex : ℂ) = (((H.subgroupOf L)).index : ℂ) := by
            exact_mod_cast complementIndex_eq_subgroupOf_index H78
          rw [hke, hce]
          ring
  -- `‖β‖² = e + 1` via the source-side norm evaluation.
  have hsrc : H78.SourceDiffNormEvaluation :=
    H78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal_of_zeta_irreducible
      hN_ind1H
      (induce_family_orthogonal_of_injective (H.subgroupOf L) θ hinj 0 ind1H (Ne.symm hind1H))
      hzeta_irr
  -- The orthogonal expansion of `‖β‖²`.
  have hexpand := H78.betaNormSq_eq_of_source_orthogonal hBD horth_if hnorm_ne hz0_compl
    hdeg_sum hzeta_irr
  -- Cast the numeric bounds to the `H78` accessors.
  have hph' : (p : ℝ) ^ 2 ≤ (H78.kernelOrder : ℝ) := by
    rwa [show H78.kernelOrder = Nat.card ↥H from rfl]
  have h2e' : 2 * (H78.complementIndex : ℝ) ≤ (p : ℝ) + 1 := by
    have hce : H78.complementIndex = (H.subgroupOf L).index := by
      exact_mod_cast complementIndex_eq_subgroupOf_index H78
    rwa [hce]
  have h0 := betaDecomp_a_eq_zero_of_p_bounds H78 hBD
    (H78.betaNormSq_eq_complementIndex_add_one hsrc) hexpand hp3 hph' h2e'
  rwa [hBDa] at h0

open OddOrder.Peterfalvi.S09 in
/-- **The two-sided (7.7.a) evaluation over the sharp support `A = H \ {1}`** (whnf-wall
isolation wrapper).  `chiRho_apply_eq_zeta0_induced` with the three geometric inputs
(`hAconj`/`hAK_off`/`hA_one`) discharged from `A = H^#` and the normality of `H` in `L`; the
uniform coefficient identification `hc` is taken as a hypothesis, so this wrapper carries none
of the `hypothesis78OfDade` context (whose local hypotheses blow up the final unification). -/
theorem chiRho_apply_eq_zeta0_sharp
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L) (H : Subgroup G)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    [Finite ↥(H.subgroupOf L)] [Invertible (Nat.card ↥(H.subgroupOf L) : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥(H.subgroupOf L))
    (hinj : Function.Injective
      (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ) ∈
        Set.range (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
        - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdeg : ∀ i, ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
        = d i * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
    (hζ0norm : ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))
      (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)) = 1)
    (χ : ClassFunction G ℂ)
    (hc : ∀ i : Fin (n + 1), i ≠ 0 →
      ClassFunction.inner (H71.τ ⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ), psi_support i⟩)
        χ = -(d i))
    {x : ↥L} (hx : (x : G) ∈ A) :
    H71.chiRho χ x = ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) x := by
  haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  exact chiRho_apply_eq_zeta0_induced H71 (H.subgroupOf L) θ d psi_support hinj hcover hdeg
    (supportInSubgroup_sharp_conj_mem_iff H hAH hHnorm)
    (fun _ hy => supportInSubgroup_sharp_subset_subgroupOf H hAH hy)
    (one_not_mem_supportInSubgroup_sharp H hAH) hζ0norm χ hc hx

set_option maxHeartbeats 800000 in
-- raised heartbeat budget for the heavy elaboration below
open OddOrder.Peterfalvi.S09 in
/-- **Peterfalvi (12.14), `ψ^ρ(x) = χ(x)` for the Dade-realized family.**  In the setting of
`betaDecompOfDade_a_eq_zero` (whose numerics force the (7.8.a) coefficient `a = 0`), the coherent
image `ψ = ν ζ_0` of the distinguished `ζ_0 = Ind θ_0` satisfies Peterfalvi's (12.14)
evaluation `ψ^ρ(x) = ζ_0(x)` at every `x ∈ A`.

The (7.7.a) coefficients collapse uniformly: for `i ≠ 0, ind1H` the coherence agreement and
`ν`-isometry give `c_i = −d_i` (`cCoeff_nu_zeta_zero_eq_neg_d`); at `i = ind1H`,
`c_{ind1H} = (β, ζ_0^ν) = a − 1 = −1 = −d_{ind1H}` by the `a = 0` counting and `d_{ind1H} = 1`.
The two-sided (7.7.a) evaluation `chiRho_apply_eq_zeta0_induced` then matches `ψ^ρ` with `ζ_0`
term by term on `A`. -/
theorem chiRho_nu_zeta0_apply_eq_zeta0_ofDade
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    [Fintype ↥(H.subgroupOf L)] [Invertible (Nat.card ↥(H.subgroupOf L) : ℂ)] {n : ℕ}
    (θ : Fin (n + 1) → IrreducibleCharacter ↥(H.subgroupOf L))
    (hinj : Function.Injective
      (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥(H.subgroupOf L),
      ClassFunction.induce (H.subgroupOf L) (φ : ClassFunction _ ℂ) ∈
        Set.range (fun i => ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
    (d : Fin (n + 1) → ℂ)
    (psi_support : ∀ i, (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
        - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdeg : ∀ i, ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ) (1 : ↥L)
        = d i * ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L))
    (ind1H : Fin (n + 1)) (hind1H : ind1H ≠ 0)
    (hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥(H.subgroupOf L))
    (hdeg_match : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
        = ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ) (1 : ↥L))
    (ν : ClassFunction ↥L ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)))
          (ν (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce (H.subgroupOf L) (θ j : ClassFunction _ ℂ)))
    (hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      H71.τ ⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = ν (ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ))
          - d i • ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)))
    (hzeta0nu : ClassFunction.inner (ν (ClassFunction.induce (H.subgroupOf L)
        (θ 0 : ClassFunction _ ℂ))) (Hypothesis71.constOne G) = 0)
    (hζ0norm : ClassFunction.inner (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))
      (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)) = 1)
    (a : ℤ) (ha : (a : ℂ) = ClassFunction.inner
      (hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H
        hzeta_ind1H hdeg_match ν hnu_isometry hagree).beta
      (ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))) + 1)
    (hzeta_irr : IsIrreducibleCharacter
      (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)))
    {p : ℕ} (hp3 : 3 ≤ p)
    (hph : (p : ℝ) ^ 2 ≤ (Nat.card ↥H : ℝ))
    (h2e : 2 * (((H.subgroupOf L).index : ℝ)) ≤ (p : ℝ) + 1)
    {x : ↥L} (hx : (x : G) ∈ A) :
    H71.chiRho (ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))) x
      = ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) x := by
  haveI hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  set H78 := hypothesis78OfDade H71 hτ H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H
    hind1H hzeta_ind1H hdeg_match ν hnu_isometry hagree with hH78
  -- `a = 0` (the (12.14) counting).
  have ha0 : a = 0 := betaDecompOfDade_a_eq_zero H71 hτ H hHL hHnorm hAH θ hinj hcover d
    psi_support hdeg ind1H hind1H hzeta_ind1H hdeg_match ν hnu_isometry hagree hzeta0nu hζ0norm
    a ha hzeta_irr hp3 hph h2e
  have hz0 : ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (θ 0)
  -- The uniform coefficient identification `⟨ψ_i^τ, ν ζ_0⟩ = −d_i` (`i ≥ 1`), computed
  -- directly (no `H78` field projections beyond `beta`, avoiding the whnf-wall).
  have hdind : d ind1H = 1 := by
    have h := hdeg ind1H
    rw [← hdeg_match] at h
    field_simp [hz0] at h
    exact h.symm
  have hc : ∀ i : Fin (n + 1), i ≠ 0 →
      ClassFunction.inner (H71.τ ⟨ClassFunction.induce (H.subgroupOf L) (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ), psi_support i⟩)
        (ν (ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ))) = -(d i) := by
    intro i hi0
    by_cases hii : i = ind1H
    · -- `⟨ψ_{ind1H}^τ, νζ_0⟩ = ⟨β, νζ_0⟩ = a − 1 = −1 = −d_{ind1H}`.
      rw [hii]
      have hβ : H71.τ ⟨ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ)
            - d ind1H • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ),
          psi_support ind1H⟩ = H78.beta := by
        change H71.τ _ = H78.hyp76.hyp71.τ H78.indMinusZetaSupp
        congr 1
        apply Subtype.ext
        change ClassFunction.induce (H.subgroupOf L) (θ ind1H : ClassFunction _ ℂ)
            - d ind1H • ClassFunction.induce (H.subgroupOf L) (θ 0 : ClassFunction _ ℂ)
          = H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct
        rw [hdind, one_smul]
        rfl
      rw [hβ]
      have hval := ha
      rw [ha0] at hval
      push_cast at hval
      rw [hdind]
      linear_combination -hval
    · -- The off-`ind1H` computation of `cCoeff_nu_zeta_zero_eq_neg_d`, inlined.
      rw [hagree i hi0 hii, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
        hnu_isometry i 0 hii (Ne.symm hind1H),
        hnu_isometry 0 0 (Ne.symm hind1H) (Ne.symm hind1H),
        induce_family_orthogonal_of_injective (H.subgroupOf L) θ hinj i 0 hi0, hζ0norm,
        mul_one, zero_sub]
  -- Drop the `set`-introduced let-body before the final application (whnf-wall hygiene).
  clear_value H78
  clear hH78 ha ha0
  -- The two-sided (7.7.a) evaluation, through the isolation wrapper
  -- `chiRho_apply_eq_zeta0_sharp` (all arguments are fvars; the heavy `ofDade` context never
  -- meets the unification inside `chiRho_apply_eq_zeta0_induced`).
  exact chiRho_apply_eq_zeta0_sharp H71 H hHnorm hAH θ hinj hcover d psi_support hdeg hζ0norm
    _ hc hx

/-- **The Dade integral character map is ℂ-linear** (the §12→§7 coherence-bridge keystone).
`dadeIntegralCharacterMap` is `(LinearMap.exists_extend hyp.dadeLinearMap).choose.restrictScalars ℤ`
— the ℂ-linear extension of the §4 Dade map, read as `ℤ`-linear (`IntegralCharacterMap`).  Its
underlying function is therefore ℂ-linear: `τ (c • x) = c • τ x` for `c : ℂ`.  This is the missing
ingredient for the (7.8.a) coherence agreement `τ(ζ_i − d_i ζ_0) = ν ζ_i − d_i ν ζ_0` (`d_i ∈ ℚ`):
the integer-degree ℤ-combination `ζ_0(1)·ζ_i − ζ_i(1)·ζ_0 ∈ ℤ[S]` gives, via `extends_on_supported`
and division, `ν ζ_i − d_i ν ζ_0 = τ ζ_i − d_i τ ζ_0`, and this ℂ-linearity closes the gap
`τ(ζ_i − d_i ζ_0) = τ ζ_i − d_i τ ζ_0`. -/
theorem dadeIntegralCharacterMap_smul_complex {G : Type*} [Group G] {A : Set G} {L : Subgroup G}
    [Fintype G] [Fintype ↥L] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card L : ℂ)]
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (dade : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp)
    (c : ℂ) (x : ClassFunction ↥L ℂ) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade (c • x)
      = c • OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade x := by
  simp only [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap, LinearMap.restrictScalars_apply,
    map_smul]

/-- **The (7.8.a) coherence agreement from `IsCoherent`** (the §12→§7 bridge, part 1).  For a
coherent base map `τ` (ℂ-linear via `hτ_smul`, e.g. `dadeIntegralCharacterMap_smul_complex`) with
extension `ν = hcoh.extension`, and family members `ζ_i, ζ_0 ∈ S` of integer degrees `m_i, m_0`
(`m_0 ≠ 0`, `d_i = m_i/m_0`) whose difference `ζ_i − d_i ζ_0` is supported on `A`, the (7.8.a)
agreement `τ(ζ_i − d_i ζ_0) = ν ζ_i − d_i ν ζ_0` holds.

The integer-degree ℤ-combination `c = m_0·ζ_i − m_i·ζ_0 = m_0·(ζ_i − d_i ζ_0) ∈ ℤ[S]` is supported,
so `ν c = τ c` (`extends_on_supported`); ℤ-linear decomposition (natCast-smul ↔ nsmul) and division
by `m_0` give `ν ζ_i − d_i ν ζ_0 = τ ζ_i − d_i τ ζ_0`, and `τ`'s ℂ-linearity closes
`τ(ζ_i − d_i ζ_0) = τ ζ_i − d_i τ ζ_0`. -/
theorem coherence_hagree {L G : Type*} [Group L] [Group G] [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A)
    (hτ_smul : ∀ (c : ℂ) (x : ClassFunction L ℂ), τ (c • x) = c • τ x)
    {ζi ζ0 : ClassFunction L ℂ} (hζi : ζi ∈ S) (hζ0 : ζ0 ∈ S)
    {m0 mi : ℕ} (hm0_ne : (m0 : ℂ) ≠ 0) {di : ℂ} (hdi : di = (mi : ℂ) / (m0 : ℂ))
    (hsupp : (ζi - di • ζ0).support ⊆ A) :
    τ (ζi - di • ζ0) = hcoh.extension ζi - di • hcoh.extension ζ0 := by
  classical
  have hcast : ∀ (f : ClassFunction L ℂ →ₗ[ℤ] ClassFunction G ℂ) (n : ℕ) (x : ClassFunction L ℂ),
      f ((n : ℂ) • x) = (n : ℂ) • f x := fun f n x => by
    rw [Nat.cast_smul_eq_nsmul ℂ n x, map_nsmul, Nat.cast_smul_eq_nsmul ℂ n (f x)]
  have hmi_eq : (mi : ℂ) = (m0 : ℂ) * di := by rw [hdi, mul_div_cancel₀ _ hm0_ne]
  have hc_eq : (m0 : ℂ) • ζi - (mi : ℂ) • ζ0 = (m0 : ℂ) • (ζi - di • ζ0) := by
    rw [hmi_eq, smul_sub, smul_smul]
  have hc_mem : ((m0 : ℂ) • ζi - (mi : ℂ) • ζ0) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A := by
    refine ⟨?_, ?_⟩
    · rw [Nat.cast_smul_eq_nsmul ℂ m0 ζi, Nat.cast_smul_eq_nsmul ℂ mi ζ0]
      exact Submodule.sub_mem _ (nsmul_mem (Submodule.subset_span hζi) m0)
        (nsmul_mem (Submodule.subset_span hζ0) mi)
    · rw [hc_eq]
      exact (ClassFunction.support_smul_subset _ _).trans hsupp
  have hext := hcoh.extends_on_supported _ hc_mem
  rw [map_sub, map_sub, hcast, hcast, hcast, hcast, hmi_eq, mul_smul, mul_smul,
    ← smul_sub, ← smul_sub] at hext
  have eq2 : hcoh.extension ζi - di • hcoh.extension ζ0 = τ ζi - di • τ ζ0 :=
    smul_right_injective (ClassFunction G ℂ) hm0_ne hext
  rw [map_sub, hτ_smul]
  exact eq2.symm

/-- **The (7.8.a) coherence agreement in `DadeMap` form** (the §12→§7 bridge, parts 1+2 combined).
For the §12 coherent base map `τ = dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)`
(ℂ-linear by `dadeIntegralCharacterMap_smul_complex`), `coherence_hagree` gives the agreement at the
`IntegralCharacterMap` level; `dadeIntegralCharacterMap_apply_of_support` rewrites it to the
`DadeMap`
`(hyp.fullDadeIsometryData hconj).toDadeMap` on the supported difference (these agree by
`dadeIsometryData_toDadeMap`).  The result is exactly the `hagree` shape that `hypothesis78OfDade`
consumes (`H71.τ ⟨ζ_i − d_i ζ_0, _⟩ = ν ζ_i − d_i ν ζ_0` with `H71 = toHypothesis71`,
`ν = hcoh.extension`). -/
theorem coherence_hagree_dadeMap {G : Type*} [Group G] {A : Set G} {L : Subgroup G}
    [Fintype G] [Fintype ↥L] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S : Set (ClassFunction ↥L ℂ)}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {ζi ζ0 : ClassFunction ↥L ℂ} (hζi : ζi ∈ S) (hζ0 : ζ0 ∈ S)
    {m0 mi : ℕ} (hm0_ne : (m0 : ℂ) ≠ 0) {di : ℂ} (hdi : di = (mi : ℂ) / (m0 : ℂ))
    (hsupp : (ζi - di • ζ0).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L) :
    (hyp.fullDadeIsometryData hconj).toDadeMap
        ⟨ζi - di • ζ0, (ClassFunction.mem_supportedSubmodule).mpr hsupp⟩
      = hcoh.extension ζi - di • hcoh.extension ζ0 := by
  have h1 := coherence_hagree hcoh
    (dadeIntegralCharacterMap_smul_complex hyp (hyp.fullDadeIsometryData hconj)) hζi hζ0 hm0_ne hdi
    hsupp
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp
    (hyp.fullDadeIsometryData hconj) hsupp] at h1
  exact h1

/-- **The coherent extension is isometric on the family** (§12→§7 bridge, the `nu_isometry`
ingredient).  `IsCoherent.extension_inner_eq` preserves inner products on the integral span
`ℤ[S] = zSpan S`; specialised to family members `ζ_i, ζ_j ∈ S ⊆ zSpan S`, it gives
`⟨ν ζ_i, ν ζ_j⟩ = ⟨ζ_i, ζ_j⟩` — the family-level isometry the `Hypothesis78` `ν` machinery actually
consumes (every `nu_isometry` use site rewrites it on family members `zeta i`/`zeta j`).  The §12
coherent `ν = hcoh.extension` is *not* a global isometry (the `exists_extend` lift off `CF(L,A)` is
merely linear), so this family-restricted form is the load-bearing one. -/
theorem coherence_extension_inner_eq_on_family {L G : Type*} [Group L] [Group G]
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A)
    {ζi ζj : ClassFunction L ℂ} (hζi : ζi ∈ S) (hζj : ζj ∈ S) :
    ClassFunction.inner (hcoh.extension ζi) (hcoh.extension ζj)
      = ClassFunction.inner ζi ζj :=
  hcoh.extension_inner_eq ζi ζj (Submodule.subset_span hζi) (Submodule.subset_span hζj)

/-- **Two orthonormal integral characters with equal `1_G`-coefficient are both orthogonal to
`1_G`** (the linear-algebra core of the coherent `⊥1_G` fact, Peterfalvi (7.8.a)).

If `x, y ∈ ℤ[Irr G]` are norm-`1` (`⟨x,x⟩ = ⟨y,y⟩ = 1`), orthogonal (`⟨x,y⟩ = 0`), and have the
*same* inner product with the trivial character (`⟨x,1_G⟩ = ⟨y,1_G⟩ =: c`), then `c = 0`.

Proof: by (5.9.a) `exists_zsmul_irreducibleCharacter_of_inner_self_one`, `x = ε·ξ`, `y = δ·ζ`
with `ε, δ = ±1` and `ξ, ζ` irreducible.  Orthogonality forces `ξ ≠ ζ`, so at most one of `ξ, ζ`
is the trivial character.  If `ξ` is trivial then `ζ` is not, giving `c = ⟨y,1_G⟩ = 0` while
`c = ⟨x,1_G⟩ = ±1`, a contradiction; hence `ξ` is nontrivial and `c = ⟨x,1_G⟩ = ε·0 = 0`. -/
theorem inner_constOne_eq_zero_of_orthonormal_pair {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {x y : ClassFunction G ℂ} (hx : x ∈ ZIrr G) (hy : y ∈ ZIrr G)
    (hxnorm : ClassFunction.inner x x = 1) (hynorm : ClassFunction.inner y y = 1)
    (hxy : ClassFunction.inner x y = 0)
    (hc : ClassFunction.inner x (Hypothesis71.constOne G)
        = ClassFunction.inner y (Hypothesis71.constOne G)) :
    ClassFunction.inner x (Hypothesis71.constOne G) = 0 := by
  classical
  obtain ⟨ε, ξ, hε, rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hx hxnorm
  obtain ⟨δ, ζ, hδ, rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hy hynorm
  -- `1_G` as the trivial irreducible character (both are the all-ones class function).
  have hco : Hypothesis71.constOne G = (trivialIrreducibleCharacter G : ClassFunction G ℂ) := rfl
  -- `⟨m•μ, 1_G⟩ = m · [μ = 1_G]` for an irreducible `μ`.
  have key : ∀ (m : ℤ) (μ : IrreducibleCharacter G),
      ClassFunction.inner (m • (μ : ClassFunction G ℂ)) (Hypothesis71.constOne G)
        = (m : ℂ) * (if μ = trivialIrreducibleCharacter G then 1 else 0) := by
    intro m μ
    rw [hco, ← Int.cast_smul_eq_zsmul ℂ m (μ : ClassFunction G ℂ),
      ClassFunction.inner_smul_left, irreducibleCharacter_inner]
  -- Orthogonality forces `ξ ≠ ζ`.
  have hξζ : ξ ≠ ζ := by
    intro h; subst h
    rw [← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ),
      ← Int.cast_smul_eq_zsmul ℂ δ (ξ : ClassFunction G ℂ),
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_right,
      irreducibleCharacter_inner, if_pos rfl, mul_one] at hxy
    have hεne : (ε : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by rcases hε with h | h <;> simp [h])
    have hδne : star (δ : ℂ) ≠ 0 := by
      rw [star_ne_zero]; exact Int.cast_ne_zero.mpr (by rcases hδ with h | h <;> simp [h])
    exact (mul_ne_zero hεne hδne) hxy
  rw [key ε ξ] at hc ⊢
  rw [key δ ζ] at hc
  by_cases hξ : ξ = trivialIrreducibleCharacter G
  · -- `ξ` trivial ⟹ `ζ` nontrivial ⟹ `c = 0` from `y`, but `c = ±1` from `x`.
    exfalso
    have hζ : ζ ≠ trivialIrreducibleCharacter G := fun h => hξζ (hξ.trans h.symm)
    rw [if_pos hξ, mul_one, if_neg hζ, mul_zero] at hc
    rcases hε with h | h <;> rw [h] at hc <;> norm_num at hc
  · rw [if_neg hξ, mul_zero]

/-- **The coherent image of a distinguished member is orthogonal to `1_G`** (Peterfalvi (7.8.a),
the `⟨ζ_0^ν, 1_G⟩ = 0` fact — the certificate that the abstract `IsCoherent` structure does not
carry directly, recovered here from a *second* member of `S` of the **same degree**).

Given the coherence `hcoh` (with `τ` `ℂ`-linear via `hτ_smul`, and `htau1` the Dade `⊥1_G`
transport `⟨τ φ, 1_G⟩ = ⟨φ, 1_L⟩` on `A`-supported `φ`), and two members `ζ_0, ζ_0' ∈ S` that are
norm-`1`, orthogonal, both `⊥ 1_L`, with `ζ_0' − ζ_0` `A`-supported (i.e. equal degree), the images
`ν ζ_0, ν ζ_0'` are orthonormal in `ℤ[Irr G]` with equal `1_G`-coefficient (the equal-degree Dade
difference is `⊥ 1`), so `inner_constOne_eq_zero_of_orthonormal_pair` forces `⟨ν ζ_0, 1_G⟩ = 0`.

The canonical second member is the complex conjugate `ζ_0' = ζ̄_0`
(§12 `Sset_closedUnderConjugate`), distinct from `ζ_0` by the odd order of `L`
(no nontrivial real irreducible). -/
theorem coherence_extension_orthogonal_constOne {L G : Type*} [Group L] [Group G]
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ S A)
    (hτ_smul : ∀ (c : ℂ) (x : ClassFunction L ℂ), τ (c • x) = c • τ x)
    (htau1 : ∀ φ : ClassFunction L ℂ, φ.support ⊆ A →
        ClassFunction.inner (τ φ) (Hypothesis71.constOne G)
          = ClassFunction.inner φ (Hypothesis71.constOne L))
    {ζ0 ζ0' : ClassFunction L ℂ} (hζ0 : ζ0 ∈ S) (hζ0' : ζ0' ∈ S)
    (hnorm0 : ClassFunction.inner ζ0 ζ0 = 1) (hnorm0' : ClassFunction.inner ζ0' ζ0' = 1)
    (horth : ClassFunction.inner ζ0 ζ0' = 0)
    (hsupp : (ζ0' - ζ0).support ⊆ A)
    (hζ0_1 : ClassFunction.inner ζ0 (Hypothesis71.constOne L) = 0)
    (hζ0'_1 : ClassFunction.inner ζ0' (Hypothesis71.constOne L) = 0) :
    ClassFunction.inner (hcoh.extension ζ0) (Hypothesis71.constOne G) = 0 := by
  have hxZ : hcoh.extension ζ0 ∈ ZIrr G := hcoh.extension_mem_ZIrr ζ0 (Submodule.subset_span hζ0)
  have hyZ : hcoh.extension ζ0' ∈ ZIrr G := hcoh.extension_mem_ZIrr ζ0' (Submodule.subset_span hζ0')
  have hxn : ClassFunction.inner (hcoh.extension ζ0) (hcoh.extension ζ0) = 1 := by
    rw [coherence_extension_inner_eq_on_family hcoh hζ0 hζ0]; exact hnorm0
  have hyn : ClassFunction.inner (hcoh.extension ζ0') (hcoh.extension ζ0') = 1 := by
    rw [coherence_extension_inner_eq_on_family hcoh hζ0' hζ0']; exact hnorm0'
  have hxy : ClassFunction.inner (hcoh.extension ζ0) (hcoh.extension ζ0') = 0 := by
    rw [coherence_extension_inner_eq_on_family hcoh hζ0 hζ0']; exact horth
  have hc : ClassFunction.inner (hcoh.extension ζ0) (Hypothesis71.constOne G)
      = ClassFunction.inner (hcoh.extension ζ0') (Hypothesis71.constOne G) := by
    have hd := coherence_hagree hcoh hτ_smul hζ0' hζ0 (m0 := 1) (mi := 1) (di := 1)
      (by norm_num) (by norm_num) (by simpa using hsupp)
    simp only [one_smul] at hd
    have hτval : ClassFunction.inner (τ (ζ0' - ζ0)) (Hypothesis71.constOne G)
        = ClassFunction.inner (ζ0' - ζ0) (Hypothesis71.constOne L) := htau1 (ζ0' - ζ0) hsupp
    rw [hd, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left, hζ0'_1, hζ0_1,
      sub_zero] at hτval
    exact (sub_eq_zero.mp hτval).symm
  exact inner_constOne_eq_zero_of_orthonormal_pair hxZ hyZ hxn hyn hxy hc

end OddOrder.Peterfalvi.S09.Cert

