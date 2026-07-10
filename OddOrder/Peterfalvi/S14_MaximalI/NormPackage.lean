/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S14_MaximalI.RhoMEvaluation

/-!
# Peterfalvi (12.16) — the witness value/norm package and the final contradiction

The capstone of §12: the `CounterexampleDadeData` character/norm contract, its construction
`exists_counterexample_dade_data` from the witness Dade calculation ((12.13)–(12.15) + the
(7.3)/(7.8.b) norm bounds), the (12.16) contradiction `counterexample_contradiction`, and its
headline consequences `pi_empty` / `typeI_frobenius` ((12.7)).

Split from `DadeContradiction.lean` (file-size policy); the `ρ_M` machinery it consumes is in
`RhoMEvaluation.lean`, the `ρ`-side witness bounds in `DadeContradiction.lean`.
-/
namespace OddOrder.Peterfalvi.S14
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8.b), the witness `hB` for a *given* Dade calculation** — the parametric form
of `witness_L_zeta_bound`, producing the (7.8.b) norm lower bound for the specific witness Dade
character `ψ = dade.psi` of a *given* `(hyp, coh, dade)` triple (rather than existentially
producing its own): `1 − e/|H| ≤ ‖ψ^ρ‖²`, where `ρ` is the (7.1) `A(L)`-based `chiRhoCF` of
`hyp` and `e = dade.e = [L:H]`.

Rebuilds the witness `Hypothesis78` with the placed family **anchored at `dade.chi`**
(`exists_placed_induced_family` applied to `χ_dist := dade.chi ∈ S`, which is `Ind θ_lin` for a
nontrivial `θ_lin` by the family shape), so the distinguished member is
`ζ_0 = Ind (θ 0) = dade.chi` and the (7.8.b) bound `1 − e/h ≤ ‖ζ_0^{νρ}‖²`
(`zetaNuRhoNormSqGeOfDade`) lands, via `ν = coh.extension` and `ψ = coh.extension dade.chi`,
exactly on `‖chiRhoCF dade.psi‖²` — the `normRho` that the (12.16) `hC` shares. -/
theorem witness_dade_psi_rho_norm_ge [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (dade : DadeNotation hyp)
    (hψeq : dade.psi = coh.extension dade.chi)
    (he_eq : dade.e = ((hyp.typeI.typeF.H).subgroupOf data.L).index) :
    (1 : ℝ) - (dade.e : ℝ) / (Nat.card ↥(hyp.typeI.typeF.H) : ℝ)
      ≤ (ClassFunction.inner (hyp.toHypothesis71.chiRhoCF dade.psi)
          (hyp.toHypothesis71.chiRhoCF dade.psi)).re := by
  classical
  -- The Frobenius witness for `L`, transported to `hyp`'s kernel accessor.
  obtain ⟨frob, -⟩ := witness_L_frobenius hG data
  have hHfrob : hyp.typeI.typeF.H = frob.typeI.typeF.H := by
    rw [hyp.typeI.typeF.H_eq, frob.typeI.typeF.H_eq]
  have hC : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥data.L
      ((hyp.typeI.typeF.H).subgroupOf data.L) frob.complement := by
    rw [hHfrob]; exact frob.frobenius
  have hHL : hyp.typeI.typeF.H ≤ data.L := hyp.typeI.typeF.H_le
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf data.L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal data.L
  have hAH : typeIA data.L hyp.typeI = (hyp.typeI.typeF.H : Set G) \ {1} :=
    witness_typeIA_eq_sharp hG data hyp
  have hHnorm : ∀ (l : ↥data.L) {h : G}, h ∈ hyp.typeI.typeF.H →
      (l : G) * h * (l : G)⁻¹ ∈ hyp.typeI.typeF.H := by
    intro l h hh
    have hhL : h ∈ data.L := hHL hh
    have hmem : (⟨h, hhL⟩ : ↥data.L) ∈ (hyp.typeI.typeF.H).subgroupOf data.L :=
      (Subgroup.mem_subgroupOf).mpr hh
    have hconj := hKnormal.conj_mem ⟨h, hhL⟩ hmem l
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  -- The placed family anchored at the distinguished `dade.chi`.
  obtain ⟨θlin, hθlin_ne, hχ_eq⟩ := dade.chi_mem
  obtain ⟨n, θ, ind1H, hind1H, h0, htriv, hinj, hcover⟩ :=
    OddOrder.Peterfalvi.S09.Cert.exists_placed_induced_family
      ((hyp.typeI.typeF.H).subgroupOf data.L) dade.chi ⟨θlin, hχ_eq.symm⟩
      (hχ_eq ▸ OddOrder.Peterfalvi.S09.Cert.induce_ne_trivialChar_induce
        ((hyp.typeI.typeF.H).subgroupOf data.L) θlin hθlin_ne)
  -- `Ind (θ 0)(1) = [L:H]`, from `dade.chi(1) = e = [L:H]`.
  have hdeg0 : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
      (θ 0 : ClassFunction _ ℂ) (1 : ↥data.L)
      = (((hyp.typeI.typeF.H).subgroupOf data.L).index : ℂ) := by
    rw [h0]
    rw [show dade.chi (1 : ↥data.L) = ((dade.e : ℕ) : ℂ) from dade.chi_degree_eq_e, he_eq]
  have hSmem : ∀ i, i ≠ ind1H →
      ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)
        ∈ hyp.Sset := by
    intro i hi
    refine ⟨θ i, fun htriv_i => hi (hinj ?_), rfl⟩
    change ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ ind1H : ClassFunction _ ℂ)
    rw [htriv_i, htriv]
  have hθ0_ne : θ 0 ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf data.L) := by
    intro h
    refine hind1H (hinj ?_).symm
    change ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ 0 : ClassFunction _ ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ ind1H : ClassFunction _ ℂ)
    rw [h, htriv]
  let d : Fin (n + 1) → ℂ :=
    fun i => (θ i : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L) ℂ)
      (1 : ↥((hyp.typeI.typeF.H).subgroupOf data.L))
  have hd : ∀ i, d i = (θ i : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L) ℂ)
      (1 : ↥((hyp.typeI.typeF.H).subgroupOf data.L)) := fun _ => rfl
  have hdeg : ∀ i, ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ) (1 : ↥data.L)
      = d i * ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥data.L) := by
    intro i
    rw [ClassFunction.induce_apply_one ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ), hdeg0, hd i]
    ring
  have hdeg_match : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥data.L)
      = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ ind1H : ClassFunction _ ℂ) (1 : ↥data.L) := by
    rw [hdeg0, htriv]
    change (((hyp.typeI.typeF.H).subgroupOf data.L).index : ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
          (trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L)) (1 : ↥data.L)
    rw [induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)]
  have psi_support : ∀ i, (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ)
      - d i • ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
          (θ 0 : ClassFunction _ ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA data.L hyp.typeI) data.L := by
    intro i
    refine (induce_diff_support (θ i) (θ 0) (d i) (hdeg i)).trans ?_
    intro x hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr ⟨hx.1, hx.2⟩
  have hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (coh.extension
          (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)))
          (coh.extension
          (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ j : ClassFunction _ ℂ)))
        = ClassFunction.inner
          (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ))
          (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ j : ClassFunction _ ℂ)) :=
    fun i j hi hj => coherence_extension_inner_eq_on_family coh (hSmem i hi) (hSmem j hj)
  have hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      hyp.toHypothesis71.τ ⟨ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
          (θ i : ClassFunction _ ℂ)
          - d i • ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
            (θ 0 : ClassFunction _ ℂ), psi_support i⟩
        = coh.extension (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
            (θ i : ClassFunction _ ℂ))
          - d i • coh.extension (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
            (θ 0 : ClassFunction _ ℂ)) := by
    intro i _ hi_ind
    obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ i)
    exact coherence_hagree_dadeMap hyp.dadeData.dade hyp.hconj coh
      (hSmem i hi_ind) (hSmem 0 (Ne.symm hind1H)) (m0 := 1) (mi := deg_i) (by norm_num)
      (by rw [hd i, hdeg_i_eq, Nat.cast_one, div_one]) (psi_support i)
  -- The concrete witness `Hypothesis78`, anchored at `ζ_0 = dade.chi`.
  set H78 := hypothesis78OfDade hyp.toHypothesis71
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeIsometry
    hyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv hdeg_match
    coh.extension hnu_isometry hagree with hH78def
  -- (7.8) input `a`: `(β, ζ_0^ν) + 1 ∈ ℤ`.
  obtain ⟨a, ha⟩ := exists_betaDecomp_a H78
    (Submodule.sub_mem _
      (ClassFunction.induce_mem_ZIrr _ (θ ind1H).property.mem_ZIrr)
      (ClassFunction.induce_mem_ZIrr _ (θ 0).property.mem_ZIrr))
    (coh.extension_mem_ZIrr _ (Submodule.subset_span (hSmem 0 (Ne.symm hind1H))))
  -- (7.8.b) `smallIndex`: `2e + 1 ≤ h`, from the Frobenius size bound.
  have hodd : Odd (Nat.card ↥data.L) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card data.L)
  have hKodd : Odd (Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hCodd : Odd (Nat.card ↥frob.complement) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card frob.complement)
  have hKcard : Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L) = Nat.card hyp.typeI.typeF.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  have hKnt : ((hyp.typeI.typeF.H).subgroupOf data.L) ≠ ⊥ := by
    haveI : Nontrivial ↥hyp.typeI.typeF.H :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hyp.typeI.typeF.H_nontrivial
    haveI : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf data.L) :=
      (Subgroup.subgroupOfEquivOfLe hHL).toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  have hcompl : Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L) * Nat.card ↥frob.complement
      = Nat.card ↥data.L := hC.isComplement.card_mul_card
  have hsmall : H78.smallIndex := by
    have hfrob := frobenius_two_mul_card_complement_add_one_le_card_kernel hC hKodd hCodd hKnt
    show 2 * H78.complementIndex + 1 ≤ H78.kernelOrder
    have hke : H78.kernelOrder = Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L) := by
      rw [hKcard]; rfl
    have hce : H78.complementIndex = Nat.card ↥frob.complement := by
      show Nat.card ↥data.L / Nat.card hyp.typeI.typeF.H = Nat.card ↥frob.complement
      rw [← hKcard, ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
    rw [hke, hce]; exact hfrob
  -- The (7.8.b) bound for `H78`.
  have hbound : 1 - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤ H78.zetaNuRhoNormSq :=
    zetaNuRhoNormSqGeOfDade hyp.toHypothesis71
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeIsometry
      hyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
      hdeg_match coh.extension hnu_isometry hagree
      (witness_L_hzeta0nu hG hyp hC coh hAH (θ 0) hθ0_ne)
      (inner_self_induce_eq_one_of_frobeniusGroup hC (θ 0) hθ0_ne) a ha hsmall
  -- Identify the three `H78` projections with the `dade.psi` shape.
  have hke : H78.kernelOrder = Nat.card ↥(hyp.typeI.typeF.H) := rfl
  have hce : H78.complementIndex
      = Nat.card ↥data.L / Nat.card ↥(hyp.typeI.typeF.H) := rfl
  have hznorm : H78.zetaNuRhoNormSq
      = (ClassFunction.inner (hyp.toHypothesis71.chiRhoCF dade.psi)
          (hyp.toHypothesis71.chiRhoCF dade.psi)).re := by
    show (ClassFunction.inner
        (hyp.toHypothesis71.chiRhoCF (coh.extension (ClassFunction.induce
          ((hyp.typeI.typeF.H).subgroupOf data.L) (θ 0 : ClassFunction _ ℂ))))
        (hyp.toHypothesis71.chiRhoCF (coh.extension (ClassFunction.induce
          ((hyp.typeI.typeF.H).subgroupOf data.L) (θ 0 : ClassFunction _ ℂ))))).re = _
    rw [h0, ← hψeq]
  -- `dade.e = [L:H] = |L|/|H|` matches the `complementIndex`.
  have hidx_card : ((hyp.typeI.typeF.H).subgroupOf data.L).index
      = Nat.card ↥data.L / Nat.card ↥(hyp.typeI.typeF.H) := by
    have h1 : Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L)
        * ((hyp.typeI.typeF.H).subgroupOf data.L).index = Nat.card ↥data.L :=
      Subgroup.card_mul_index _
    rw [hKcard] at h1
    exact (Nat.div_eq_of_eq_mul_right Nat.card_pos h1.symm).symm
  rw [hke, hce, hznorm] at hbound
  have he2 : (dade.e : ℝ)
      = ((Nat.card ↥data.L / Nat.card ↥(hyp.typeI.typeF.H) : ℕ) : ℝ) := by
    rw [he_eq, hidx_card]
  rw [← he2] at hbound
  exact hbound

/-- **Peterfalvi (12.13)–(12.16), the character/norm contract** packaging every fact that the
numerical endgame `counterexample_contradiction_of_facts` consumes.  Bundling them here isolates the
deep §7/§12 content — the Dade calculation `ψ = χ^{τ₁}` of (12.13), the coset/value facts
(12.14)/(12.15), and the `ρ`/`ρM` integral inequalities (7.3)/(7.8.b) — into a single
faithfully-typed obligation, leaving the (12.16) capstone `counterexample_contradiction` a
`sorry`-free assembly.

Field map to the textbook (`H = L_F`, the Fitting kernel of the witness subgroup `L`):
* `ε`/`hε` — a primitive `p`-th root of unity (the cyclotomic base of (1.10));
* `ψ`/`hψ` — the virtual character `ψ = χ^{τ₁}` of (12.13) (`ZIrr` membership = it is a
  ℤ-combination of irreducibles, from the Dade isometry image);
* `e` — the common degree `χ(1) = e` of the coherent family `S` ((12.6)); `he`/`h2e` = (12.12);
* `h_const` = (12.14) (`ψ` constant on the coset `xK`); `h_psix` = (1.10.a) applied to `χ`;
  `h_psig_int` = (12.15) (`ψ(g) ∈ ℤ`);
* `kK`/`kKp`/`kM`/`kH` = `|K|`/`|K'|`/`|M|`/`|H|`; `hidx` = (8.1.c), `hM` = (12.11);
* `hA` = (12.15) norm relation for `ρM`, `hB` = (7.8.b) for `ρ`, `hC` = (7.3)+(8.17). -/
structure CounterexampleDadeData {ctr : CounterexampleHypothesis (G := G)}
    (witness : RankTwoWitnessData ctr) (g : G) where
  ε : ℂ
  hε : IsPrimitiveRoot ε ctr.p
  ψ : ClassFunction G ℂ
  hψ : ψ ∈ ZIrr G
  e : ℤ
  mval : ℤ
  he : 3 ≤ e
  h2e : 2 * e ≤ (ctr.p : ℤ) + 1
  h_const : ψ (witness.x * g) = ψ witness.x
  h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ ψ witness.x - (e : ℂ) = (1 - ε) * w
  h_psig_int : ψ g = (mval : ℂ)
  kK : ℝ
  kKp : ℝ
  kM : ℝ
  kH : ℝ
  normRhoM : ℝ
  normRho : ℝ
  hkKp : 0 < kKp
  hkM : 0 < kM
  hkH : 0 < kH
  hidx : 4 * kKp ≤ kK
  hM : kM ≤ kK * kH
  hA : (kK - kKp) / kM * (mval : ℝ) ^ 2 ≤ normRhoM
  hB : (1 : ℝ) - (e : ℝ) / kH ≤ normRho
  hC : normRhoM + normRho < 1

/-! The former `witness_psi_degree` obligation (`ψ(1) = e`, the coherent-extension degree
preservation) has been **removed**: Peterfalvi's (12.16) does not use it.  The `h_psix`
congruence `ψ(x) ≡ e (mod 1 − ε)` is instead supplied by the proven (12.14) evaluation
`ψ(x) = χ(x)` (`witness_dade_psi_apply_x_eq_chi`) combined with the `L`-side (1.10.a)
congruence `χ(x) ≡ χ(1) = e` — see `exists_counterexample_dade_data`. -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.14)/(12.15) + (7.3)/(7.8.b)/(8.17), the witness value/norm package** — the
deep §7/§12 content the (12.16) contradiction consumes beyond the arithmetic, bundled as one
faithfully-typed obligation for the specific witness Dade character `ψ = dade.psi`.

Concretely, for the (12.9) witness `L` with its (12.13) Dade calculation `ψ = χ^{τ₁}` of degree
`e = dade.e = [L:H]`, and the commuting `g ∈ C_K(x) ∖ K'`, it supplies:
* `mval`, `h_psig_int` — (12.15): `ψ(g) ∈ ℤ` (`ψ` constant on `K − K′`, integer-valued there);
* `h_const` — (12.14): `ψ(x·g) = ψ(x)` (`ψ` constant on the coset `xK`);
* `hidx` — the fixed-point-free `[K:K'] ≥ 4` of (8.1.c), as `4·|K'| ≤ |K|`;
* `h2e` — the degree bound `2e ≤ p+1` of (12.12);
* `normRhoM`, `normRho`, `hA`, `hB`, `hC` — the `ρ`/`ρM` norm estimates: `hA` = (12.15) norm
  relation `‖ψ^{ρM}‖² ≥ (|K−K'|/|M|)·ψ(g)²`, `hB` = (7.8.b) `‖ψ^ρ‖² ≥ 1 − e/|H|`, `hC` =
  (7.3)+(8.17) `‖ψ^{ρM}‖² + ‖ψ^ρ‖² < 1`.

**Genuinely still-missing**: the `ρ`-machinery norm estimates (`S09.zetaNuRhoNormSqGeOfDade` for
`hB`, `chiRho_integral_inequality`/(8.17) support-disjointness for `hC`, the (12.15) `ρM` relation
for `hA`), the (12.3)/(12.5) constancy facts feeding `h_const`/(12.15), and the (8.1.c)/(12.12)
numerics `hidx`/`h2e` for the witness are none of them assembled into these exact conclusions in
reach of `S14`.  The statement is **sound**: each conjunct is the genuine
(12.14)/(12.15)/(12.12)/(8.1.c)/(7.x)
fact for the *specific* witness character `ψ = dade.psi` of the genuine witness `L` (tied to
`ctr`/`witness`/`hyp`/`dade` via `data` and `hψZ`), with `e = dade.e` and `|K|,|K'|,|M|,|H|` the
genuine cardinalities — not a free arithmetic implication. -/
theorem witness_value_norm_package [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (data : RankTwoWitnessData ctr) (hLeq : L = data.L)
    {g : G} (hg_comm : Commute data.x g) (hgK : g ∈ ctr.K) (hgK' : g ∉ ctr.Kprime)
    (hyp : Hypothesis L) (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (dade : DadeNotation hyp)
    (hψeq : dade.psi = coh.extension dade.chi)
    (he_eq : dade.e = ((hyp.typeI.typeF.H).subgroupOf L).index) (hψZ : dade.psi ∈ ZIrr G) :
    ∃ (mval : ℤ) (normRhoM normRho : ℝ),
      dade.psi (data.x * g) = dade.psi data.x ∧
      dade.psi g = (mval : ℂ) ∧
      2 * (dade.e : ℤ) ≤ (ctr.p : ℤ) + 1 ∧
      4 * (Nat.card ↥ctr.Kprime : ℝ) ≤ (Nat.card ↥ctr.K : ℝ) ∧
      ((Nat.card ↥ctr.K : ℝ) - (Nat.card ↥ctr.Kprime : ℝ)) / (Nat.card ↥ctr.M : ℝ)
          * (mval : ℝ) ^ 2 ≤ normRhoM ∧
      (1 : ℝ) - (dade.e : ℝ) / (Nat.card ↥(hyp.typeI.typeF.H) : ℝ) ≤ normRho ∧
      normRhoM + normRho < 1 := by
  sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.13)–(12.15) + (7.3)/(7.8.b)**, the construction of the character/norm contract
of (12.16).  Given the rank-two witness of (12.9) and a commuting element `g ∈ C_K(x) ∖ K'`
(`exists_witness_g`), the §7/§12 machinery produces the Dade calculation `ψ = χ^{τ₁}` and its
associated `ρ`/`ρM` norm bounds.

**Assembly** (`sorry`-free modulo the two genuine deep pins): the (12.6) coherence
`witness_L_coherent` + the distinguished `χ ∈ S` (`exists_distinguished_char`, degree `e = [L:H]`)
realize the (12.13) `dade = dadeNotation_of_coherence …` with `ψ = coh.extension χ ∈ ZIrr G`; then
each `CounterexampleDadeData` field is discharged:
* `ε`/`hε` — a primitive `p`-th root of unity (`Complex.isPrimitiveRoot_exp`);
* `e := dade.e = [L:H]`, `he : 3 ≤ e` from `three_le_index` (`|U|` odd `> 1`);
* `kK`/`kKp`/`kM`/`kH` := `|K|`/`|K'|`/`|M|`/`|H|` with positivity from `Nat.card_pos`, and
  `hM : |M| ≤ |K|·|H|` from `card_M_le` (12.11);
* `h_psix` from the proven (12.14) evaluation `ψ(x) = χ(x)` (`witness_dade_psi_apply_x_eq_chi`)
  and the `L`-side (1.10.a) congruence `χ(x) ≡ χ(1) = e (mod 1 − ε)`;
* `mval`/`h_const`/`h_psig_int`/`h2e`/`hidx`/`hA`/`hB`/`hC` from the deep value/norm package
  `witness_value_norm_package` (the (12.14)/(12.15)/(12.12)/(8.1.c)/(7.x) content). -/
theorem exists_counterexample_dade_data [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (ctr : CounterexampleHypothesis (G := G))
    (witness : RankTwoWitnessData ctr) {g : G}
    (hg_comm : Commute witness.x g) (hgK : g ∈ ctr.K) (hgK' : g ∉ ctr.Kprime) :
    Nonempty (CounterexampleDadeData witness g) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- The witness (12.13) Dade calculation with its proven (12.14) evaluation `ψ(x) = χ(x)`.
  obtain ⟨hyp, coh, dade, hψeq, he_eq, hψZ, hχZ, hψx_eq⟩ :=
    witness_dade_psi_apply_x_eq_chi hG witness
  -- A primitive `p`-th root of unity.
  obtain ⟨ε, hε⟩ : ∃ ε : ℂ, IsPrimitiveRoot ε ctr.p :=
    ⟨_, Complex.isPrimitiveRoot_exp ctr.p ctr.p_prime.pos.ne'⟩
  -- `3 ≤ e = [L:H]`.
  have hthree : 3 ≤ dade.e := he_eq ▸ three_le_index hG hyp
  -- (12.14) + the `L`-side (1.10.a): `ψ(x) = χ(x) ≡ χ(1) = e (mod 1 − ε)` (`h_psix`),
  -- with no coherent-extension degree identity `ψ(1) = e` needed.
  have hxL : witness.x ∈ witness.L := witness_x_mem_L hG witness
  have hxp : (⟨witness.x, hxL⟩ : ↥witness.L) ^ ctr.p = 1 := by
    apply Subtype.ext
    push_cast
    exact witness.x_mem_omega1
  obtain ⟨w, hw, hweq⟩ := OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute
    ctr.p_prime.pos hε hχZ hxp (Commute.one_right _)
  rw [mul_one, dade.chi_degree_eq_e] at hweq
  have h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ dade.psi witness.x - (dade.e : ℂ) = (1 - ε) * w := by
    refine ⟨w, hw, ?_⟩
    rw [hψx_eq]
    exact hweq
  -- `H = L_F` (kernel of the witness) has the same order as the maximal nilpotent normal Hall.
  have hHcard : (Nat.card ↥(hyp.typeI.typeF.H) : ℝ)
      = (Nat.card ↥(maxNilpotentNormalHall witness.L) : ℝ) := by
    rw [hyp.typeI.typeF.H_eq]
  -- The deep value/norm package (12.14)/(12.15)/(12.12)/(8.1.c)/(7.x).
  obtain ⟨mval, normRhoM, normRho, h_const, h_psig_int, h2e, hidx, hA, hB, hC⟩ :=
    witness_value_norm_package hG witness rfl hg_comm hgK hgK' hyp coh dade hψeq he_eq hψZ
  -- `|M| ≤ |K|·|H|` (12.11).
  have hM : (Nat.card ↥ctr.M : ℝ)
      ≤ (Nat.card ↥ctr.K : ℝ) * (Nat.card ↥(maxNilpotentNormalHall witness.L) : ℝ) := by
    have := card_M_le hG witness
    calc (Nat.card ↥ctr.M : ℝ)
        ≤ ((Nat.card ↥ctr.K * Nat.card ↥(maxNilpotentNormalHall witness.L) : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = (Nat.card ↥ctr.K : ℝ) * (Nat.card ↥(maxNilpotentNormalHall witness.L) : ℝ) := by
          push_cast; ring
  exact ⟨{
    ε := ε
    hε := hε
    ψ := dade.psi
    hψ := hψZ
    e := (dade.e : ℤ)
    mval := mval
    he := by exact_mod_cast hthree
    h2e := h2e
    h_const := h_const
    h_psix := h_psix
    h_psig_int := h_psig_int
    kK := (Nat.card ↥ctr.K : ℝ)
    kKp := (Nat.card ↥ctr.Kprime : ℝ)
    kM := (Nat.card ↥ctr.M : ℝ)
    kH := (Nat.card ↥(maxNilpotentNormalHall witness.L) : ℝ)
    normRhoM := normRhoM
    normRho := normRho
    hkKp := by exact_mod_cast (Nat.card_pos (α := ↥ctr.Kprime))
    hkM := by exact_mod_cast (Nat.card_pos (α := ↥ctr.M))
    hkH := by exact_mod_cast (Nat.card_pos (α := ↥(maxNilpotentNormalHall witness.L)))
    hidx := hidx
    hM := hM
    hA := hA
    hB := by
      -- `(↑(dade.e : ℤ) : ℝ) = (dade.e : ℝ)` and `|H| = |maxNilpotentNormalHall L|`.
      rw [show (((dade.e : ℤ) : ℝ)) = (dade.e : ℝ) by push_cast; ring, ← hHcard]
      exact hB
    hC := hC }⟩

/-- **Peterfalvi (12.16)**: the minimal counterexample of (12.8) is impossible.

The rank-two witness of (12.9) (`exists_rankTwoWitness`) and the commuting element `g ∈ C_K(x) ∖ K'`
(`exists_witness_g`) are extracted unconditionally; the deep §7/§12 character calculation is bundled
into `exists_counterexample_dade_data`; the contradiction then follows from the numerical endgame
`counterexample_contradiction_of_facts`. -/
theorem counterexample_contradiction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    False := by
  obtain ⟨_, _, ⟨witness⟩⟩ := exists_rankTwoWitness hG ctr
  obtain ⟨g, hg_comm, hgK, hgK'⟩ := exists_witness_g witness
  obtain ⟨d⟩ := exists_counterexample_dade_data hG ctr witness hg_comm hgK hgK'
  exact counterexample_contradiction_of_facts ctr.p_prime d.hε d.hψ witness.x_mem_omega1 hg_comm
    d.he d.h2e d.h_const d.h_psix d.h_psig_int d.hkKp d.hkM d.hkH d.hidx d.hM d.hA d.hB d.hC

/-- **Peterfalvi (12.7), `π = ∅`** (the headline consequence of (12.16)): no prime lies in the
set `π` of (12.8).  Were `π` nonempty, (12.8) (`exists_counterexampleHypothesis`) would build a
minimal counterexample, contradicting (12.16) (`counterexample_contradiction`). -/
theorem pi_empty [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∀ q : ℕ, q.Prime → ¬ InPi (G := G) q := by
  by_contra h
  push Not at h
  obtain ⟨ctr⟩ := exists_counterexampleHypothesis hG h
  exact counterexample_contradiction hG ctr

/-- **Peterfalvi (12.7)**: every maximal subgroup of type I is Frobenius, with kernel `M_F`.

Since `π = ∅` by (12.16) (`pi_empty`), the easy direction `typeI_frobenius_of_pi_empty` applies
and gives the Frobenius decomposition with kernel `M_F = typeF.H` and complement `typeF.U`.  (The
`kernel_eq_MF` carrier is vacuous here: the `frobenius` field already names `typeF.H = M_F` as the
kernel, so the identification holds definitionally.) -/
theorem typeI_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M) :
    ∃ data : TypeIFrobeniusData M, data.kernel_eq_MF := by
  obtain ⟨data⟩ := hType
  exact ⟨{ typeI := data
           complement := data.typeF.U.subgroupOf M
           kernel_eq_MF := True
           kernel_eq_MF_holds := trivial
           frobenius := typeI_frobenius_of_pi_empty hG (pi_empty hG) hM data }, trivial⟩

/-- **The type-I Dade support is `H#`** (Peterfalvi (8.3)/(12.1) for the witness subgroup `L`).
`typeIA L = centralizerSupport (H#) L` collapses to `H# = (H : Set G) \ {1}` (`H = L_F`): the
Frobenius structure of `L` (from (12.7) `typeI_frobenius`) makes the centralizer condition vacuous
on `H#` (`IsFrobeniusGroup.centralizer_kernel_le`).  This supplies the `A = H#` shape that
`S09.Cert.hypothesis78OfDade` needs (the `hAH` argument of the §12→§7 Dade bridge).

Re-derives the `centralizerSupport = sharp` argument of
`S16.centralizerSupport_sharpSubgroup_eq_of_frobenius` — which lives downstream of `S14` and so
cannot be cited here; a hub dedup hoisting that pure-group-theory fact to a shared file (e.g.
`MaximalSubgroupType`) is tracked in issue 1013. -/
theorem Hypothesis.typeIA_eq_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.GroupTheory.typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H := by
  obtain ⟨fdata, _⟩ := typeI_frobenius hG hyp.maximal ⟨hyp.typeI⟩
  have hKf : fdata.typeI.typeF.H = hyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, hyp.typeI.typeF.H_eq]
  exact hyp.typeIA_eq_sharp_of_frobenius (hKf ▸ fdata.frobenius)

end OddOrder.Peterfalvi.S14
