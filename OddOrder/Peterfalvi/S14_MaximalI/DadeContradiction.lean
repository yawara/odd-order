import OddOrder.Peterfalvi.S14_MaximalI.MinimalCounterexample

/-!
# Peterfalvi (12.13)-(12.17) + (8.8) case-(b) dichotomy

Split from the former monolithic `OddOrder.Peterfalvi.S14_MaximalI` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S14
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ## (12.13)--(12.16): Dade notation and contradiction -/

/-- **Peterfalvi (12.13)**: notation for the final Dade calculation in the
minimal counterexample. -/
structure DadeNotation {L : Subgroup G} (hyp : Hypothesis L) where
  e : ℕ
  e_eq_index : Prop
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  chi : ClassFunction ↥L ℂ
  chi_mem : chi ∈ hyp.Sset
  chi_degree_eq_e : chi 1 = (e : ℂ)
  psi : ClassFunction G ℂ
  psi_eq_tau1_chi : psi = tau1 chi
  rhoFormula : Prop
  rhoMFormula : Prop

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.13), the Dade calculation realized from coherence**: given the (12.6) coherent
extension of `L`'s family `S` (`S07.IsCoherent`, supplied by `witness_L_coherent`) and a distinguished
character `χ ∈ S` of degree `e`, the (12.13) `DadeNotation` is realized with `τ₁ =` the coherent
extension and `ψ = χ^{τ₁} = extension χ`.

This wires the coherent isometric extension into the `ψ`-construction backbone of (12.16): the
former opaque `tau1`/`psi` are now the genuine `coh.extension` and its value on `χ`.  The remaining
input is the *selection* of the distinguished `χ` — a minimal-degree `Ind_H^L θ` with `θ` a
nontrivial linear character of `H = L_F`, so `χ(1) = [L:H] = e` — together with the (12.12) degree
bounds on `e`.  (`e_eq_index`/`rhoFormula`/`rhoMFormula` remain the structure's carried `Prop`s.) -/
noncomputable def dadeNotation_of_coherence {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (χ : ClassFunction ↥L ℂ) (hχ : χ ∈ hyp.Sset) (e : ℕ) (hdeg : χ 1 = (e : ℂ)) :
    DadeNotation hyp where
  e := e
  e_eq_index := e = (hyp.H.subgroupOf L).index
  tau1 := coh.extension
  chi := χ
  chi_mem := hχ
  chi_degree_eq_e := hdeg
  psi := coh.extension χ
  psi_eq_tau1_chi := rfl
  rhoFormula := True
  rhoMFormula := True

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.13), the distinguished character**: the family `S` of `L` contains a member of
minimal degree `[L : H]` (`H = L_F`), namely `Ind_H^L θ` for `θ` a nontrivial **linear** character
of `H`.  Such `θ` exists because `H = L_F` is a nontrivial nilpotent group, so its commutator is
proper (`H` is not perfect); `exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`
then supplies a nontrivial degree-one `θ`, and `induce_apply_one` gives the induced degree
`[L:H]·θ(1) = [L:H]`.  This is the distinguished `χ ∈ S` with `χ(1) = e = [L:H]` of the (12.13)/(12.16)
Dade calculation — the input to `dadeNotation_of_coherence`. -/
theorem exists_distinguished_char {L : Subgroup G} [Finite G] (hyp : Hypothesis L) :
    ∃ χ ∈ hyp.Sset, χ (1 : ↥L) = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  have hHL : hyp.typeI.typeF.H ≤ L := hyp.typeI.typeF.H_le
  have e : ↥((hyp.typeI.typeF.H).subgroupOf L) ≃* ↥(hyp.typeI.typeF.H) :=
    Subgroup.subgroupOfEquivOfLe hHL
  haveI : Nontrivial ↥(hyp.typeI.typeF.H) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hyp.typeI.typeF.H_nontrivial
  haveI : Group.IsNilpotent ↥(hyp.typeI.typeF.H) :=
    hyp.typeI.typeF.H_eq ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
  haveI : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf L) := e.toEquiv.nontrivial
  haveI : IsSolvable ↥((hyp.typeI.typeF.H).subgroupOf L) :=
    solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  have hcomm : commutator ↥((hyp.typeI.typeF.H).subgroupOf L) ≠ ⊤ :=
    (IsSolvable.commutator_lt_top_of_nontrivial _).ne
  obtain ⟨θ, hθ_ne, hθ_deg⟩ :=
    OddOrder.Peterfalvi.S08.exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top
      hcomm
  have hmem : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∈ hyp.Sset :=
    ⟨θ, hθ_ne, rfl⟩
  refine ⟨_, hmem, ?_⟩
  rw [ClassFunction.induce_apply_one, hθ_deg, mul_one]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The placed induced family for the witness `L`** (§12→§7 bridge, the `θ`/`ind1H` shape
`hypothesis78OfDade` consumes).  Applies `exists_placed_induced_family` to the distinguished
`χ = Ind θ_lin ∈ S` of `exists_distinguished_char` (`θ_lin` nontrivial linear, so `χ ≠ Ind 1_K` by
`induce_ne_trivialChar_induce`): the distinguished char lands at index `0` with induced degree
`[L:K]` (`= e`), the trivial char `1_K` lands at some `ind1H ≠ 0`, and the family is
injective/covering.  `K = (L_F).subgroupOf L` is normal in `L` (`maxNilpotentNormalHall_..._normal`).
This is the family input to the witness-`L` `Hypothesis78`. -/
theorem exists_witness_placed_family {L : Subgroup G} [Finite G] (hyp : Hypothesis L) :
    ∃ (n : ℕ) (θ : Fin (n + 1) → IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))
      (ind1H : Fin (n + 1)),
      ind1H ≠ 0 ∧
      ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ 0 : ClassFunction _ ℂ) (1 : ↥L) = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) ∧
      θ ind1H = trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) ∧
      Function.Injective (fun i => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ i : ClassFunction _ ℂ)) ∧
      ∀ φ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
        ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (φ : ClassFunction _ ℂ) ∈
          Set.range (fun i => ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
            (θ i : ClassFunction _ ℂ)) := by
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  obtain ⟨χ, hχ, hdeg⟩ := exists_distinguished_char hyp
  obtain ⟨θlin, hθ_ne, hχ_eq⟩ := hχ
  obtain ⟨n, θ, ind1H, hind, h0, htriv, hinj, hcov⟩ :=
    OddOrder.Peterfalvi.S09.Cert.exists_placed_induced_family ((hyp.typeI.typeF.H).subgroupOf L) χ
      ⟨θlin, hχ_eq.symm⟩
      (hχ_eq ▸ OddOrder.Peterfalvi.S09.Cert.induce_ne_trivialChar_induce
        ((hyp.typeI.typeF.H).subgroupOf L) θlin hθ_ne)
  exact ⟨n, θ, ind1H, hind, by rw [h0]; exact hdeg, htriv, hinj, hcov⟩

/-- **Peterfalvi (12.13)/(12.16), the degree lower bound `e ≥ 3`**: the distinguished degree
`e = [L:H]` (`H = L_F`) of a type-I `Hypothesis` is at least `3`.  It equals the order of the
Frobenius complement `U` (`H` complements `U` in `L`, `typeF.complement`), which is **nontrivial**
(`typeF.U_nontrivial`) and of **odd** order (a subgroup of the odd-order `G`); an odd integer `> 1`
is `≥ 3`.  This discharges the `he : 3 ≤ e` field of `CounterexampleDadeData`. -/
theorem three_le_index {L : Subgroup G} [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis L) :
    3 ≤ ((hyp.typeI.typeF.H).subgroupOf L).index := by
  -- `[L : H] = |U|` via the complement `H ⋊ U = L`.
  have hUle : hyp.typeI.typeF.U ≤ L := hyp.typeI.typeF.U_le
  have hidx_eq : ((hyp.typeI.typeF.H).subgroupOf L).index = Nat.card ↥(hyp.typeI.typeF.U) := by
    rw [hyp.typeI.typeF.complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle).toEquiv]
  -- `|U| > 1` (nontrivial) and `|U|` odd (divides `|G|` odd), so `|U| ≥ 3`.
  haveI : Nontrivial ↥(hyp.typeI.typeF.U) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hyp.typeI.typeF.U_nontrivial
  have hgt1 : 1 < ((hyp.typeI.typeF.H).subgroupOf L).index := by
    rw [hidx_eq]; exact Finite.one_lt_card
  have hodd : Odd ((hyp.typeI.typeF.H).subgroupOf L).index := by
    have hdvd : ((hyp.typeI.typeF.H).subgroupOf L).index ∣ Nat.card G :=
      (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card L)
    rcases Nat.even_or_odd ((hyp.typeI.typeF.H).subgroupOf L).index with hev | ho
    · exfalso
      obtain ⟨d, hd⟩ := hG.odd
      obtain ⟨m, hm⟩ := hev.two_dvd.trans hdvd
      omega
    · exact ho
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Peterfalvi (12.11)/(12.16), the index bound `|M| ≤ |K|·|H|`** (`H = L_F`): from the (12.11)
complement structure (`M ∩ L` complements `K` in `M`, and `M ∩ L ≤ L_F`), the order of `M`
factors as `|M| = |K|·|M ∩ L| ≤ |K|·|L_F|`.  This discharges the `hM` field of
`CounterexampleDadeData` (cites the (12.11) `intersection_complement_structure`). -/
theorem card_M_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Nat.card ↥ctr.M ≤ Nat.card ↥ctr.K * Nat.card ↥(maxNilpotentNormalHall data.L) := by
  obtain ⟨hcompl, hsub⟩ := intersection_complement_structure hG data
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  -- `|M| = |K| · |M ∩ L|` from the complement `K ⋊ (M ∩ L) = M`.
  have h1 : Nat.card ↥(ctr.K.subgroupOf ctr.M) * (ctr.K.subgroupOf ctr.M).index = Nat.card ↥ctr.M :=
    Subgroup.card_mul_index _
  have h2 : (ctr.K.subgroupOf ctr.M).index = Nat.card ↥((ctr.M ⊓ data.L).subgroupOf ctr.M) :=
    hcompl.symm.index_eq_card
  have h3 : Nat.card ↥(ctr.K.subgroupOf ctr.M) = Nat.card ↥ctr.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have h4 : Nat.card ↥((ctr.M ⊓ data.L).subgroupOf ctr.M) = Nat.card ↥(ctr.M ⊓ data.L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hMeq : Nat.card ↥ctr.M = Nat.card ↥ctr.K * Nat.card ↥(ctr.M ⊓ data.L) := by
    rw [← h3, ← h4, ← h2, h1]
  -- `|M ∩ L| ≤ |L_F|` since `M ∩ L ≤ L_F`.
  have hle : Nat.card ↥(ctr.M ⊓ data.L) ≤ Nat.card ↥(maxNilpotentNormalHall data.L) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hsub)
  rw [hMeq]
  exact Nat.mul_le_mul_left _ hle

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.13) for the witness subgroup `L`**: the second maximal `L` of (12.9) carries a
full (12.13) `DadeNotation` — the realized `ψ = χ^{τ₁}` of the (12.16) Dade calculation.

Assembles the foundation chain: `witness_L_coherent` supplies the (12.6) coherent extension of `L`'s
family `S`, `exists_distinguished_char` selects the distinguished `χ ∈ S` of degree `[L:H]`, and
`dadeNotation_of_coherence` realizes the (12.13) notation with `τ₁ = ` the coherent extension and
`ψ = χ^{τ₁}`.  This is the `ψ`-data of `CounterexampleDadeData`; what remains for the (12.16)
contradiction is the value/norm content — (12.14)/(12.15) for `h_const`/`h_psig_int`, the (12.12)
degree bounds, and the `ρ`/`ρM` norm bounds `hA`/`hB`/`hC`. -/
theorem exists_witness_dadeNotation [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L, ∃ dade : DadeNotation hyp, dade.psi ∈ ZIrr G := by
  obtain ⟨hyp, ⟨coh⟩⟩ := witness_L_coherent hG data
  obtain ⟨χ, hχ, hdeg⟩ := exists_distinguished_char hyp
  refine ⟨hyp, dadeNotation_of_coherence hyp coh χ hχ
    ((hyp.typeI.typeF.H).subgroupOf data.L).index hdeg, ?_⟩
  -- `dade.psi = coh.extension χ` and `χ ∈ S ⊆ ℤ[S]`, so the coherent extension lands in `ℤ[Irr G]`.
  exact coh.extension_mem_ZIrr χ (Submodule.subset_span hχ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.14)**: the character `dade.psi` is constant on the coset `x·K`.

**Assembly** (the (12.4) coset-constancy applied to the counterexample `M`): since `M` is type-I
(`ctr.M_typeI`), it carries its own Hypothesis (`exists_typeI_hypothesis`), whose kernel is
`H_M = M_F = ctr.K` (`typeF.H_eq` + `K_eq_MF`).  Applying (12.4)
(`orthogonal_character_constant_on_coset`) to this `Hypothesis M` with `x = witness.x ∈ P₀ ≤ M`
gives `dade.psi(x·g) = dade.psi(x)` for `g ∈ H_M = K`, provided the two inputs:
* `horth`: `dade.psi ⊥ R_M(χ)` for `χ ∈ S_M` — the cross-group orthogonality `L ≠ M`
  (`coherent_extension_constituent_orthogonal_Rset_of_nonconjugate`, since `dade.psi = coh.extension χ_L`
  lies in `ℤ[R(χ_L)]` and `R(χ_L) ⊥ R(χ_M)`); needs the coherence `coh` and `L ≠ M` in scope;
* `hxK`: `x ∉ K` — `x` is a nontrivial `p`-element and `p ∤ |K| = |M_F|` (`K` is the `p'`-Hall `M_F`). -/
theorem psi_constant_on_xK [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (witness : RankTwoWitnessData ctr) (dade : DadeNotation hyp)
    {chi0 : IrreducibleCharacter ↥L}
    (data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥L ℂ))
    (hchi0 : chi0 ∈ data0.constituents)
    (hchi0_mem : (chi0 : ClassFunction ↥L ℂ) ∈ hyp.Sset)
    (hpsi : dade.psi = coh.extension (chi0 : ClassFunction ↥L ℂ))
    (hLM : ¬ ∃ g : G, MulAut.conj g • L = ctr.M) :
    ∀ g : G, g ∈ ctr.K → dade.psi (witness.x * g) = dade.psi witness.x := by
  classical
  obtain ⟨hypM⟩ := exists_typeI_hypothesis hG ctr.M_maximal ctr.M_typeI
  have hHK : hypM.H = ctr.K := hypM.typeI.typeF.H_eq.trans ctr.K_eq_MF.symm
  have data_M : ∀ χ ∈ hypM.Sset, CharacterDecompositionData hypM χ :=
    fun χ hχ => (character_decomposition_and_dade_domain hG hypM hχ).choose
  -- (12.3)/(5.5) cross-group orthogonality `dade.psi ⊥ R_M` (the genuine content; `M ≠ L`):
  -- `dade.psi = coh.extension χ₀ ∈ ℤ[R(χ₀)]` and `R(χ₀) ⊥ R_M` since `L ≠ M`.
  have horth : ∀ χ (hχ : χ ∈ hypM.Sset), ∀ α ∈ Rset (data_M χ hχ),
      ClassFunction.inner dade.psi α = 0 := by
    intro χ hχ α hα
    rw [hpsi]
    exact coherent_extension_constituent_orthogonal_Rset_of_nonconjugate hG hyp coh data0 hchi0
      hchi0_mem hypM hLM (data_M χ hχ) α hα
  have hxM : witness.x ∈ ctr.M := ctr.P0_le_M witness.x_mem_P0
  -- `x ∉ K`: nontrivial `p`-element, `p ∤ |K|` (K = M_F is the `p'`-Hall since `p ∣ [M:M_F]`).
  have hxK : witness.x ∉ hypM.H := by
    rw [hHK]
    intro hxmem
    haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
    have hord : orderOf witness.x = ctr.p :=
      orderOf_eq_prime witness.x_mem_omega1 witness.x_ne_one
    -- `p = orderOf x ∣ |K|`.
    have hpK : ctr.p ∣ Nat.card ↥ctr.K := by
      have hd := orderOf_dvd_natCard (⟨witness.x, hxmem⟩ : ↥ctr.K)
      have he : orderOf (⟨witness.x, hxmem⟩ : ↥ctr.K) = ctr.p := by
        rw [← hord]
        exact (orderOf_injective ctr.K.subtype ctr.K.subtype_injective _).symm
      rwa [he] at hd
    -- `Coprime |K| [M:K]` (Hall) and `p ∣ [M:K]` ⟹ contradiction.
    have hKleM : ctr.K ≤ ctr.M :=
      ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
    have hcard : Nat.card ↥(ctr.K.subgroupOf ctr.M) = Nat.card ↥ctr.K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
    have hcop : Nat.Coprime (Nat.card ↥ctr.K) (ctr.K.relIndex ctr.M) := by
      have h := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M).coprime_index
      rw [← ctr.K_eq_MF, hcard] at h
      rwa [Subgroup.relIndex]
    exact Nat.Prime.not_dvd_one ctr.p_prime (hcop ▸ Nat.dvd_gcd hpK ctr.p_dvd_index)
  intro g hg
  exact orthogonal_character_constant_on_coset hG hypM data_M horth hxM hxK g (hHK ▸ hg)

/-- The witness `x` lies in `L` (via `x ∈ P₀ ⊆ L_F ≤ L`, Peterfalvi (12.10)). -/
theorem witness_x_mem_L [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    data.x ∈ data.L :=
  OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le data.L
    (witness_P0_le_kernel hG data data.x_mem_P0)

/-- **Peterfalvi (12.1)/(12.10) for the witness `L`: `A(L) = L_F^#`** — the (12.7)-free form.
The witness `L` is Frobenius by (12.10) (`witness_L_frobenius`, proved from minimality alone), so
`typeIA_eq_sharp_of_frobenius` applies directly.  The general `Hypothesis.typeIA_eq_sharp` routes
through (12.7) `typeI_frobenius` = `pi_empty` = the (12.16) contradiction itself, so it must not
be used in the (12.16) supply chain (circularity). -/
theorem witness_typeIA_eq_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L) :
    OddOrder.GroupTheory.typeIA data.L hyp.typeI = (hyp.typeI.typeF.H : Set G) \ {1} := by
  obtain ⟨frob, -⟩ := witness_L_frobenius hG data
  have hKf : frob.typeI.typeF.H = hyp.typeI.typeF.H := by
    rw [frob.typeI.typeF.H_eq, hyp.typeI.typeF.H_eq]
  exact hyp.typeIA_eq_sharp_of_frobenius (hKf ▸ frob.frobenius)

/-- The witness `x` lies in the type-I support `A(L) = L_F^#` (Peterfalvi (12.1)/(12.10)):
`x ∈ P₀ ⊆ L_F = typeF.H` and `x ≠ 1`. -/
theorem witness_x_mem_typeIA [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L) :
    data.x ∈ OddOrder.GroupTheory.typeIA data.L hyp.typeI := by
  rw [witness_typeIA_eq_sharp hG data hyp]
  refine Set.mem_diff_of_mem ?_ (by simpa using data.x_ne_one)
  rw [SetLike.mem_coe, hyp.typeI.typeF.H_eq]
  exact witness_P0_le_kernel hG data data.x_mem_P0

/-- **The witness maximal pin `𝓜(C_G(x)) = {M}`** (Peterfalvi (12.9)/(12.14), the `N[x] = M`
identification).  The witness `x ∈ Ω₁(P₀)^# ⊆ L_F = L_σ` is a `σ`-sharp element of `L` escaping
`L` (`C_G(x) ⊄ L`, (12.9)), so the BG Theorem-D singleton
(`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`) pins a unique
maximal over `C_G(x)`; it is `M` because `C_G(x) ≤ N_G(⟨x⟩) ≤ M` ((12.9)). -/
theorem witness_maximalContaining_centralizer_eq_singleton [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    OddOrder.GroupTheory.maximalSubgroupsContaining
      (Subgroup.centralizer ({data.x} : Set G)) = {ctr.M} := by
  classical
  have hLtypeI : IsTypeI data.L := witness_L_isTypeI hG data
  have hLF_eq : maxNilpotentNormalHall data.L = OddOrder.BG.Ch3.S10.Msigma data.L :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG data.L_maximal).2.2.2.2.2.mpr
      (Or.inl hLtypeI)
  have hxσ : data.x ∈ OddOrder.BG.Ch4.S14.sigmaSharp data.L :=
    ⟨hLF_eq ▸ witness_P0_le_kernel hG data data.x_mem_P0, by simpa using data.x_ne_one⟩
  have hCM : Subgroup.centralizer ({data.x} : Set G) ≤ ctr.M := by
    refine le_trans ?_ data.normalizer_closure_x_le_M
    rw [← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  obtain ⟨N₀, hN₀⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG data.L_maximal hxσ data.centralizer_x_not_le_L
  have hMN₀ : ctr.M = N₀ := by
    have hMin : ctr.M ∈ OddOrder.GroupTheory.maximalSubgroupsContaining
        (Subgroup.centralizer ({data.x} : Set G)) := ⟨ctr.M_maximal, hCM⟩
    rw [hN₀] at hMin
    exact hMin
  rw [hN₀, hMN₀]

/-- **Peterfalvi (12.14), `R(x) = C_K(x) ⊆ K`** (Definition (8.14) at the witness): the faithful
Dade kernel of the witness `x` lands in `K = M_F`.  On the escaping branch the kernel is
`R(x) = (N[x])_σ ⊓ C_G(x)` with `N[x] = M` (the singleton pin
`witness_maximalContaining_centralizer_eq_singleton`) and `M_σ = M_F = K` for the type-I
counterexample (`MF_eq_Msigma`); the non-escaping branch is `⊥`.  Stated for an arbitrary
support set `A` (the escaping branch does not depend on it). -/
theorem witness_ftSupportKernel_le_K [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    {A : Set G} :
    OddOrder.Peterfalvi.S10.ftSupportKernel data.L A data.x ≤ ctr.K := by
  classical
  by_cases hesc : data.x ∈ OddOrder.GroupTheory.escapingCentralizerSet data.L A
  · rw [OddOrder.Peterfalvi.S10.ftSupportKernel_eq_of_escaping hesc]
    -- The branch condition of `FT_signalizerBase`: `1 < |𝓜_σ(x)|` and `𝓜(C_G(x)) ≠ ∅`.
    have hLtypeI : IsTypeI data.L := witness_L_isTypeI hG data
    have hLF_eq : maxNilpotentNormalHall data.L = OddOrder.BG.Ch3.S10.Msigma data.L :=
      (OddOrder.BG.Ch4.S16.proposition_type_classification hG data.L_maximal).2.2.2.2.2.mpr
        (Or.inl hLtypeI)
    have hxLσ : data.x ∈ OddOrder.BG.Ch3.S10.Msigma data.L :=
      hLF_eq ▸ witness_P0_le_kernel hG data data.x_mem_P0
    have hsing := witness_maximalContaining_centralizer_eq_singleton hG data
    have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement data.x).ncard := by
      by_contra h
      push Not at h
      exact data.centralizer_x_not_le_L
        (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG data.L_maximal hxLσ
          data.x_ne_one h)
    have hne : (OddOrder.GroupTheory.maximalSubgroupsContaining
        (Subgroup.centralizer ({data.x} : Set G))).Nonempty := by
      rw [hsing]
      exact ⟨ctr.M, rfl⟩
    have hcond : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement data.x).ncard ∧
        (OddOrder.GroupTheory.maximalSubgroupsContaining
          (Subgroup.centralizer ({data.x} : Set G))).Nonempty := ⟨hgt, hne⟩
    -- `N[x] = M`: the chosen member of the singleton `𝓜(C_G(x)) = {M}`.
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase data.x = hcond.2.choose := dif_pos hcond
    have hch : hcond.2.choose ∈ ({ctr.M} : Set (Subgroup G)) :=
      (Set.ext_iff.mp hsing _).mp hcond.2.choose_spec
    have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase data.x = ctr.M :=
      hb.trans (Set.mem_singleton_iff.mp hch)
    calc OddOrder.BG.Ch4.S16.FT_signalizer data.x
        ≤ OddOrder.BG.Ch3.S10.Msigma (OddOrder.BG.Ch4.S16.FT_signalizerBase data.x) :=
          inf_le_left
      _ = ctr.K := by rw [hbase, ← MF_eq_Msigma hG ctr]
  · rw [OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping hesc]
    exact bot_le

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.14), the `ψ^ρ(x) = ψ(x)` collapse**: any `χ ∈ CF(G)` constant on the coset
`x·K` (e.g. `ψ = dade.psi`, via `psi_constant_on_xK`) has `ρ`-average at the witness `x` equal to
its value: `χ^ρ(x) = χ(x)`.  The local Dade kernel is `H(x) = R(x) ⊆ K`
(`H_eq_ftSupportKernel` + `witness_ftSupportKernel_le_K`), so the `x·K`-constancy restricts to
the `H(x)`-coset and the `ρ`-average collapses (`chiRho_apply_eq_of_forall_coset`). -/
theorem witness_chiRho_apply_eq_of_forall_K [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L) (χ : ClassFunction G ℂ)
    (hconst : ∀ g : G, g ∈ ctr.K → χ (data.x * g) = χ data.x)
    (hxL : data.x ∈ data.L) :
    hyp.toHypothesis71.chiRho χ ⟨data.x, hxL⟩ = χ data.x := by
  have hxA : ((⟨data.x, hxL⟩ : ↥data.L) : G) ∈ OddOrder.GroupTheory.typeIA data.L hyp.typeI :=
    witness_x_mem_typeIA hG data hyp
  refine OddOrder.Peterfalvi.S09.Hypothesis71.chiRho_apply_eq_of_forall_coset
    hyp.toHypothesis71 χ hxA ?_
  intro y hy
  refine hconst y (witness_ftSupportKernel_le_K hG data
    (A := OddOrder.GroupTheory.typeIA data.L hyp.typeI) ?_)
  rw [← hyp.dadeData.H_eq_ftSupportKernel ⟨data.x, hxA⟩]
  exact hy

/-- **The witness `L` is not conjugate to `M`** ((12.14): "`p` divides `|L_s|` but not `|M_s|`").
`P₀ ≤ L_F = L_σ` gives `p ∣ |L_σ|`, while `|M_σ| = |K|` is prime to `p` (`p_not_dvd_card_K`);
a conjugation `L^g = M` would carry `L_σ` onto `M_σ` (`Msigma_conj_smul`), contradiction. -/
theorem witness_L_not_conj_M [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ¬ ∃ g : G, MulAut.conj g • data.L = ctr.M := by
  rintro ⟨g, hg⟩
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `p ∣ |P₀| ∣ |L_σ|`.
  have hLtypeI : IsTypeI data.L := witness_L_isTypeI hG data
  have hLF_eq : maxNilpotentNormalHall data.L = OddOrder.BG.Ch3.S10.Msigma data.L :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG data.L_maximal).2.2.2.2.2.mpr
      (Or.inl hLtypeI)
  have hP0le : ctr.P0 ≤ OddOrder.BG.Ch3.S10.Msigma data.L :=
    hLF_eq ▸ witness_P0_le_kernel hG data
  haveI : Nontrivial ↥ctr.P0 := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact ctr.P0_noncyclic isCyclic_of_subsingleton
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ctr.P0_pGroup
  have hpP0 : ctr.p ∣ Nat.card ↥ctr.P0 := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero] at hn
      exact absurd hn Finite.one_lt_card.ne'
    · rw [hn]
      exact dvd_pow_self _ hpos.ne'
  have hpLσ : ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma data.L) :=
    hpP0.trans (Subgroup.card_dvd_of_le hP0le)
  -- Transport along the conjugation: `|L_σ| = |(L^g)_σ| = |M_σ| = |K|`.
  have hcard : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma data.L)
      = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M) := by
    rw [← hg, OddOrder.BG.Ch4.S14.Msigma_conj_smul]
    exact Nat.card_congr
      (Subgroup.equivSMul (MulAut.conj g) (OddOrder.BG.Ch3.S10.Msigma data.L)).toEquiv
  rw [hcard, ← MF_eq_Msigma hG ctr] at hpLσ
  exact p_not_dvd_card_K ctr hpLσ

/-- **The counterexample prime is at least `3`** (`p` is an odd prime: `p ∣ [M:K] ∣ |G|` odd). -/
theorem counterexample_three_le_p [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) : 3 ≤ ctr.p := by
  have hpG : ctr.p ∣ Nat.card G := by
    have h1 : ctr.p ∣ (ctr.K.subgroupOf ctr.M).index := by
      have := ctr.p_dvd_index
      rwa [Subgroup.relIndex] at this
    exact (h1.trans (Subgroup.index_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card ctr.M)
  have hpodd : Odd ctr.p := hG.odd.of_dvd_nat hpG
  have h2 := ctr.p_prime.two_le
  have hne : ctr.p ≠ 2 := fun h => by
    rw [h] at hpodd
    exact (by decide : ¬ Odd 2) hpodd
  omega

/-- **Peterfalvi (12.14), the `p² ≤ h` size input**: `P₀ ⊆ H = L_F` is a noncyclic `p`-group, so
`p² ∣ |P₀| ∣ |H|`. -/
theorem witness_p_sq_le_card_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L) :
    ctr.p ^ 2 ≤ Nat.card ↥(hyp.typeI.typeF.H) := by
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ctr.P0_pGroup
  -- Noncyclic forces `n ≥ 2` (order `1` and order `p` groups are cyclic).
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n
    · rw [pow_zero] at hn
      haveI : Subsingleton ↥ctr.P0 := Nat.card_eq_one_iff_unique.mp hn |>.1
      exact ctr.P0_noncyclic isCyclic_of_subsingleton
    · rw [pow_one] at hn
      exact ctr.P0_noncyclic (isCyclic_of_prime_card hn)
  have hp2 : ctr.p ^ 2 ∣ Nat.card ↥ctr.P0 := hn ▸ pow_dvd_pow _ hn2
  have hP0H : ctr.P0 ≤ hyp.typeI.typeF.H := by
    rw [hyp.typeI.typeF.H_eq]
    exact witness_P0_le_kernel hG data
  calc ctr.p ^ 2 ≤ Nat.card ↥ctr.P0 := Nat.le_of_dvd Nat.card_pos hp2
    _ ≤ Nat.card ↥(hyp.typeI.typeF.H) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hP0H)

/-- **Peterfalvi (12.12), the `2e ≤ p + 1` bound in kernel-index form**: the witness complement
order `e = [L : H]` satisfies `2e ≤ p + 1` (`two_mul_card_complement_le`, transported along
`IsComplement'.index_eq_card` and the kernel identification `typeF.H = L_F`). -/
theorem witness_two_mul_index_le_p_add_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L) :
    2 * ((hyp.typeI.typeF.H).subgroupOf data.L).index ≤ ctr.p + 1 := by
  obtain ⟨fdata, -⟩ := witness_L_frobenius hG data
  have h2e := two_mul_card_complement_le hG data fdata
  have hidx : ((fdata.typeI.typeF.H).subgroupOf data.L).index = Nat.card ↥fdata.complement :=
    fdata.frobenius.isComplement.symm.index_eq_card
  have hHeq : fdata.typeI.typeF.H = hyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, hyp.typeI.typeF.H_eq]
  rw [hHeq] at hidx
  omega

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8.a) for the witness `L`: `⟨ζ_0^ν, 1_G⟩ = 0`** (`hzeta0nu`, the last input to
the (7.8.b) bound `hB`).  The abstract `IsCoherent` does not carry orthogonality to `1_G`, but it
is recovered from the **complex conjugate** `ζ̄_0 = Ind θ̄_0 ∈ S` (`Sset_closedUnderConjugate`) — a
second member of the *same degree*, distinct from `ζ_0` because `L` has odd order (no nontrivial
real irreducible, `not_isReal_of_ne_trivial_of_odd_card'`).  `coherence_extension_orthogonal_constOne`
then forces `⟨ν ζ_0, 1_G⟩ = 0`.  Holds for **any** nontrivial `θ_0` (degree-`e`/linearity unused). -/
theorem witness_L_hzeta0nu [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (hAH : typeIA L hyp.typeI = ((hyp.typeI.typeF.H) : Set G) \ {1})
    (θ0 : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))
    (hθ0 : θ0 ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L)) :
    ClassFunction.inner
        (coh.extension (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
          (θ0 : ClassFunction _ ℂ))) (Hypothesis71.constOne G) = 0 := by
  classical
  have hodd : Odd (Nat.card ↥L) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  -- The complex conjugate character `θ̄_0` is again nontrivial irreducible.  Introduce it
  -- **opaquely** (via `obtain`, not `let`), carrying only its coercion `↑θ̄_0 = (↑θ_0)‾`: a `let`
  -- gets its coercion re-unfolded inside every `induce` coset sum, blowing the `whnf` budget.
  obtain ⟨θ0', hθ0'coe⟩ :
      ∃ t : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
        (t : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
          = (θ0 : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj :=
    ⟨⟨(θ0 : ClassFunction _ ℂ).conj, θ0.isIrreducible.conj⟩, rfl⟩
  have hθ0' : θ0' ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) := by
    intro h
    apply hθ0
    have hcoe : (θ0 : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      rw [← hθ0'coe]
      have h2 := congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
      simpa using h2
    apply Subtype.ext
    show (θ0 : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj (θ0 : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  -- The two members `ζ_0 = Ind θ_0`, `ζ̄_0 = Ind θ̄_0 ∈ S`.
  have hmem0 : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
      (θ0 : ClassFunction _ ℂ) ∈ hyp.Sset := ⟨θ0, hθ0, rfl⟩
  have hmem0' : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
      (θ0' : ClassFunction _ ℂ) ∈ hyp.Sset := ⟨θ0', hθ0', rfl⟩
  -- Norms `= 1` (Frobenius), orthogonality to `1_L`, irreducibility.
  have hnorm0 := inner_self_induce_eq_one_of_frobeniusGroup hfrob θ0 hθ0
  have hnorm0' := inner_self_induce_eq_one_of_frobeniusGroup hfrob θ0' hθ0'
  have h1_0 := inner_induce_constOne_eq_zero ((hyp.typeI.typeF.H).subgroupOf L) θ0 hθ0
  have h1_0' := inner_induce_constOne_eq_zero ((hyp.typeI.typeF.H).subgroupOf L) θ0' hθ0'
  -- `⟨ζ_0, ζ̄_0⟩ = 0` (odd-order Frobenius: `ζ_0` non-real), from the reusable general helper
  -- (`hθ0'coe : ↑θ̄_0 = (↑θ_0)‾` reindexes it to `θ_0'`).
  have horth : ClassFunction.inner
      (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (θ0 : ClassFunction _ ℂ))
      (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (θ0' : ClassFunction _ ℂ)) = 0 := by
    rw [hθ0'coe]
    exact inner_induce_conj_eq_zero_of_frobenius_of_odd hodd hfrob θ0 hθ0
  -- The equal-degree difference is `A(L) = H#`-supported.
  have hdeg' : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (θ0' : ClassFunction _ ℂ)
        (1 : ↥L)
      = 1 * ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (θ0 : ClassFunction _ ℂ)
        (1 : ↥L) := by
    rw [one_mul, ClassFunction.induce_apply_one, ClassFunction.induce_apply_one]
    congr 1
    rw [hθ0'coe, ClassFunction.conj_apply]
    obtain ⟨n, -, hn⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ0
    rw [hn, star_natCast]
  have hsupp : (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (θ0' : ClassFunction _ ℂ)
      - ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ0 : ClassFunction _ ℂ)).support ⊆ hyp.A := by
    have hds := induce_diff_support (K := (hyp.typeI.typeF.H).subgroupOf L) θ0' θ0 1 hdeg'
    rw [one_smul] at hds
    intro x hx
    have hxd := hds hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hxd
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr ⟨hxd.1, hxd.2⟩
  -- The Dade `⊥ 1_G` transport and `ℂ`-linearity of `τ = hyp.tau`.
  have htau1 : ∀ φ : ClassFunction ↥L ℂ, φ.support ⊆ hyp.A →
      ClassFunction.inner (hyp.tau φ) (Hypothesis71.constOne G)
        = ClassFunction.inner φ (Hypothesis71.constOne L) := by
    intro φ hφ
    rw [show hyp.tau φ = hyp.dadeData.dade.dadeMap
        ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ from
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) hφ]
    exact inner_tau_supported_constOne hyp.toHypothesis71
      ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
  have hτ_smul : ∀ (c : ℂ) (x : ClassFunction ↥L ℂ), hyp.tau (c • x) = c • hyp.tau x :=
    dadeIntegralCharacterMap_smul_complex hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj)
  exact coherence_extension_orthogonal_constOne coh hτ_smul htau1 hmem0 hmem0'
    hnorm0 hnorm0' horth hsupp h1_0 h1_0'

set_option maxHeartbeats 800000 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (12.14) for the witness, full form: `ψ(x) = χ(x)`.**  The witness `L` of (12.9)
carries a (12.13) Dade calculation `dade` — with `χ = dade.chi = Ind θ_0` the distinguished
degree-`e` member and `ψ = dade.psi = χ^{τ₁}` its coherent extension — whose value at the witness
`x` is `ψ(x) = χ(x)`.

Peterfalvi's proof, assembled from the three proven pieces:
* `ψ` is constant on `x·K` ((12.3)+(12.4)+(5.5): `L ≁ M` by `witness_L_not_conj_M`, then
  `psi_constant_on_xK`);
* `ψ^ρ(x) = ψ(x)` (the `ρ`-collapse: `R(x) = C_K(x) ⊆ K` per Definition (8.14), so constancy on
  `x·K` collapses the `ρ`-average — `witness_chiRho_apply_eq_of_forall_K`);
* `ψ^ρ(x) = χ(x)` (the (7.8.a) `a = 0` counting and the two-sided (7.7.a) evaluation —
  `chiRho_nu_zeta0_apply_eq_zeta0_ofDade`, fed by the witness `Hypothesis78` assembly of
  `witness_L_hypothesis78`/`witness_L_zeta_bound` plus the size inputs `3 ≤ p`
  (`counterexample_three_le_p`), `p² ≤ h` (`witness_p_sq_le_card_kernel`), and `2e ≤ p + 1`
  (`witness_two_mul_index_le_p_add_one`)).

This is the (12.16) `h_psix` feed: with the `L`-side (1.10.a) congruence
`χ(x) ≡ χ(1) = e (mod 1 − ε)` it gives `ψ(x) ≡ e (mod 1 − ε)` without the coherent-extension
degree identity `ψ(1) = e`. -/
theorem witness_dade_psi_apply_x_eq_chi [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ (hyp : Hypothesis data.L)
      (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
      (dade : DadeNotation hyp),
      dade.psi = coh.extension dade.chi ∧
      dade.e = ((hyp.typeI.typeF.H).subgroupOf data.L).index ∧
      dade.psi ∈ ZIrr G ∧
      dade.chi ∈ ZIrr ↥data.L ∧
      dade.psi data.x = dade.chi ⟨data.x, witness_x_mem_L hG data⟩ := by
  classical
  obtain ⟨hyp, C, hC, hNonTI⟩ := witness_L_hypothesis_frobenius hG data
  obtain ⟨coh⟩ : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
    rcases hyp.typeI.alternative with hTI | hab | hexp
    · exact absurd hTI hNonTI
    · exact frobenius_typeI_coherent_of_abelianKernel hG hyp ⟨C, hC⟩ hab
    · exact frobenius_typeI_coherent_of_cyclicQuotient hG hyp ⟨C, hC⟩ hexp
  have hHL : hyp.typeI.typeF.H ≤ data.L := hyp.typeI.typeF.H_le
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf data.L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal data.L
  haveI : (hyp.H.subgroupOf data.L).Normal := hKnormal
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
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ := exists_witness_placed_family hyp
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
  -- The distinguished member `ζ_0 = Ind θ_0 ∈ S` and its (12.13) Dade calculation.
  have hmem0 : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
      (θ 0 : ClassFunction _ ℂ) ∈ hyp.Sset := hSmem 0 (Ne.symm hind1H)
  set dade : DadeNotation hyp := dadeNotation_of_coherence hyp coh
    (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ 0 : ClassFunction _ ℂ))
    hmem0 ((hyp.typeI.typeF.H).subgroupOf data.L).index hdeg0 with hdade
  have hψZ : dade.psi ∈ ZIrr G := coh.extension_mem_ZIrr _ (Submodule.subset_span hmem0)
  -- (12.14) constancy: `ψ` is constant on `x·K` (via `L ≁ M`).
  have hchi0_irr : IsIrreducibleCharacter (ClassFunction.induce
      ((hyp.typeI.typeF.H).subgroupOf data.L) (θ 0 : ClassFunction _ ℂ)) :=
    Sset_isIrreducibleCharacter hyp hC hmem0
  obtain ⟨chi0, hchi0_coe⟩ : ∃ t : IrreducibleCharacter ↥data.L,
      (t : ClassFunction ↥data.L ℂ) = ClassFunction.induce
        ((hyp.typeI.typeF.H).subgroupOf data.L) (θ 0 : ClassFunction _ ℂ) :=
    ⟨⟨_, hchi0_irr⟩, rfl⟩
  have hchi0_mem : (chi0 : ClassFunction ↥data.L ℂ) ∈ hyp.Sset := by
    rw [hchi0_coe]; exact hmem0
  have data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥data.L ℂ) :=
    (character_decomposition_and_dade_domain hG hyp hchi0_mem).choose
  have hchi0_cons : chi0 ∈ data0.constituents := by
    obtain ⟨φ, hφcoe, hφmem⟩ := Sset_self_mem_constituents hyp hC hchi0_mem data0
    have hφeq : φ = chi0 := Subtype.ext hφcoe
    rwa [hφeq] at hφmem
  have hpsi_chi0 : dade.psi = coh.extension (chi0 : ClassFunction ↥data.L ℂ) := by
    rw [hchi0_coe, hdade]
    rfl
  have hconst : ∀ g : G, g ∈ ctr.K → dade.psi (data.x * g) = dade.psi data.x :=
    psi_constant_on_xK hG hyp coh data dade data0 hchi0_cons hchi0_mem hpsi_chi0
      (witness_L_not_conj_M hG data)
  -- The `ρ`-collapse `ψ^ρ(x) = ψ(x)`.
  have hxL : data.x ∈ data.L := witness_x_mem_L hG data
  have hcollapse : hyp.toHypothesis71.chiRho dade.psi ⟨data.x, hxL⟩ = dade.psi data.x :=
    witness_chiRho_apply_eq_of_forall_K hG data hyp dade.psi hconst hxL
  -- The (7.8) input `a`: `(β, ζ_0^ν) + 1 ∈ ℤ`.
  set H78 := hypothesis78OfDade hyp.toHypothesis71
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeIsometry
    hyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
    hdeg_match coh.extension hnu_isometry hagree with hH78def
  obtain ⟨a, ha⟩ := exists_betaDecomp_a H78
    (Submodule.sub_mem _
      (ClassFunction.induce_mem_ZIrr _ (θ ind1H).property.mem_ZIrr)
      (ClassFunction.induce_mem_ZIrr _ (θ 0).property.mem_ZIrr))
    (coh.extension_mem_ZIrr _ (Submodule.subset_span hmem0))
  rw [hH78def] at ha
  -- Size inputs: `3 ≤ p`, `p² ≤ h`, `2e ≤ p + 1`.
  have hp3 : 3 ≤ ctr.p := counterexample_three_le_p hG ctr
  have hph : (ctr.p : ℝ) ^ 2 ≤ (Nat.card ↥(hyp.typeI.typeF.H) : ℝ) := by
    exact_mod_cast witness_p_sq_le_card_kernel hG data hyp
  have h2e : 2 * ((((hyp.typeI.typeF.H).subgroupOf data.L).index : ℝ)) ≤ (ctr.p : ℝ) + 1 := by
    exact_mod_cast witness_two_mul_index_le_p_add_one hG data hyp
  -- The two-sided (7.7.a) evaluation `ψ^ρ(x) = ζ_0(x)`.
  have hxA : ((⟨data.x, hxL⟩ : ↥data.L) : G) ∈ typeIA data.L hyp.typeI :=
    witness_x_mem_typeIA hG data hyp
  have heval := chiRho_nu_zeta0_apply_eq_zeta0_ofDade hyp.toHypothesis71
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeIsometry
    hyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv
    hdeg_match coh.extension hnu_isometry hagree
    (witness_L_hzeta0nu hG hyp hC coh hAH (θ 0) hθ0_ne)
    (inner_self_induce_eq_one_of_frobeniusGroup hC (θ 0) hθ0_ne)
    a ha (Sset_isIrreducibleCharacter hyp hC hmem0) hp3 hph h2e hxA
  refine ⟨hyp, coh, dade, rfl, rfl, hψZ, IsIrreducibleCharacter.mem_ZIrr hchi0_irr, ?_⟩
  calc dade.psi data.x
      = hyp.toHypothesis71.chiRho dade.psi ⟨data.x, hxL⟩ := hcollapse.symm
    _ = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ 0 : ClassFunction _ ℂ) ⟨data.x, hxL⟩ := heval
    _ = dade.chi ⟨data.x, hxL⟩ := rfl


/-- **Peterfalvi (12.16), the cyclotomic congruence at `x`** (the `h_psix` field of
`CounterexampleDadeData`): for a virtual character `ψ ∈ ℤ[Irr G]`, an order-`p` element `x`, and a
primitive `p`-th root `ε`, if `ψ(1) = e` then `ψ(x) ≡ e (mod 1 - ε)`, i.e. `∃ w` integral with
`ψ(x) - e = (1 - ε)·w`.

Immediate from (1.10.a) `exists_integral_apply_sub_of_commute` at `y = 1`
(`ψ(x·1) - ψ(1) = (1-ε)·w`, since `x` commutes with `1`) and the degree hypothesis `ψ(1) = e`.  The
`ψ(1) = e` input is the coherent-extension degree preservation `dade.psi(1) = χ(1) = e` supplied by
the (12.13) construction — the one remaining ingredient of `h_psix`. -/
theorem psi_apply_x_sub_e_cyclotomic [Finite G] {p : ℕ} (hp : 0 < p) {ε : ℂ}
    (hε : IsPrimitiveRoot ε p) {ψ : ClassFunction G ℂ}
    (hψ : ψ ∈ OddOrder.RepresentationTheory.ZIrr G) {x : G} (hx : x ^ p = 1) {e : ℕ}
    (hψ1 : ψ (1 : G) = (e : ℂ)) :
    ∃ w : ℂ, IsIntegral ℤ w ∧ ψ x - (e : ℂ) = (1 - ε) * w := by
  obtain ⟨z, hz, hzeq⟩ := OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute
    hp hε hψ hx (Commute.one_right x)
  rw [mul_one, hψ1] at hzeq
  exact ⟨z, hz, hzeq⟩

/-- Virtual-character values are algebraic integers (local copy of the `S05` lemma
`isIntegral_apply_of_mem_ZIrr`, which lives in an unimported leaf): each irreducible value is a
sum of roots of unity (`character_isIntegral`), and `IsIntegral ℤ` is closed under the `ℤ`-span. -/
private theorem isIntegral_apply_of_mem_ZIrr' {φ : ClassFunction G ℂ} [Finite G]
    (hφ : φ ∈ ZIrr G) (g : G) : IsIntegral ℤ (φ g) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, hchar⟩ :=
        IsIrreducibleCharacter.isCharacter (mem_irreducibleCharacters.mp hx)
      rw [show x g = ρ.character g from congrFun hchar g]
      exact OddOrder.RepresentationTheory.character_isIntegral ρ g
  | zero => rw [ClassFunction.zero_apply]; exact isIntegral_zero
  | add a b _ _ ha hb => rw [ClassFunction.add_apply]; exact ha.add hb
  | smul n a _ ha =>
      rw [ClassFunction.zsmul_apply, zsmul_eq_mul]
      exact (isIntegral_algebraMap (x := n)).mul ha

/-- **Peterfalvi (12.15), the integrality clause** (`ψ(g) ∈ ℤ` for `g ∈ K − K′`): a virtual
character `ψ ∈ ℤ[Irr G]` that is **constant on `K − K′`** takes an integer value there.

**Honest reconstruction of the (12.15) integrality** (Coq `rhoM_psi`, final `Cint_rat_Aint` step).
Two facts combine:
* `ψ(g)` is an **algebraic integer** — the value of a virtual character
  (`isIntegral_apply_of_mem_ZIrr`);
* `ψ(g)` is **rational** — from the class-function inner-product identity
  `|K|·⟨Res_K ψ, 1_K⟩ = |K′|·⟨Res_{K′} ψ, 1_{K′}⟩ + |K − K′|·ψ(g)`.  The two inner products are
  integers (`inner_mem_ZIrr_int`, since `Res ψ` and `1` are virtual characters), and `ψ` is
  constant `= ψ(g)` on the `|K − K′|` elements of `K − K′` (the `hconst` hypothesis, which is the
  companion "`ψ` constant on `K − K′`" clause of (12.15), proven from (12.3)/(12.5)); so `ψ(g)` is a
  `ℚ`-combination of integers, i.e. rational.
A rational algebraic integer is a rational integer (`exists_int_of_isIntegral_of_mem_range_rat`).

The **constancy** hypothesis `hconst` isolates the genuine input this integrality needs; the
`ψ ∈ ZIrr G` hypothesis (the Dade image is a virtual character, by (12.13)) makes the statement
sound — for a non-virtual `ψ` the value need not be an integer.  This discharges the `h_psig_int`
field of `CounterexampleDadeData` once `ψ = dade.psi` and its `K − K′`-constancy are in place. -/
theorem rhoM_integer_values [Finite G]
    {ctr : CounterexampleHypothesis (G := G)}
    {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G)
    (hconst : ∀ g₁ g₂ : G, g₁ ∈ ctr.K → g₁ ∉ ctr.Kprime →
      g₂ ∈ ctr.K → g₂ ∉ ctr.Kprime → ψ g₁ = ψ g₂) :
    ∀ g : G, g ∈ ctr.K → g ∉ ctr.Kprime → ∃ z : ℤ, ψ g = (z : ℂ) := by
  classical
  intro g hgK hgK'
  -- `K′ = [K, K] ≤ K`.
  have hK'K : ctr.Kprime ≤ ctr.K := ctr.Kprime_eq ▸ Subgroup.map_subtype_le _
  haveI : Fintype ↥ctr.K := Fintype.ofFinite _
  haveI : Fintype ↥ctr.Kprime := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥ctr.K : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := ↥ctr.K)).ne')
  haveI : Invertible (Nat.card ↥ctr.Kprime : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := ↥ctr.Kprime)).ne')
  -- The restrictions are virtual characters; `1` is a virtual character.
  have hResK : ClassFunction.restrict ctr.K ψ ∈ ZIrr ↥ctr.K :=
    ClassFunction.restrict_mem_ZIrr ctr.K hψ
  have hResK' : ClassFunction.restrict ctr.Kprime ψ ∈ ZIrr ↥ctr.Kprime :=
    ClassFunction.restrict_mem_ZIrr ctr.Kprime hψ
  have h1K : trivialClassFunction ↥ctr.K ∈ ZIrr ↥ctr.K :=
    (trivialClassFunction_isIrreducible (G := ↥ctr.K)).mem_ZIrr
  have h1K' : trivialClassFunction ↥ctr.Kprime ∈ ZIrr ↥ctr.Kprime :=
    (trivialClassFunction_isIrreducible (G := ↥ctr.Kprime)).mem_ZIrr
  -- The two inner products are integers.
  obtain ⟨a, ha⟩ := ClassFunction.inner_mem_ZIrr_int hResK h1K
  obtain ⟨b, hb⟩ := ClassFunction.inner_mem_ZIrr_int hResK' h1K'
  -- `∑_{z:↥K} ψ(z) = |K|·⟨Res_K ψ, 1⟩`.
  have hsumK : (∑ z : ↥ctr.K, ψ (z : G)) = (Nat.card ↥ctr.K : ℂ) * (a : ℂ) := by
    have := ClassFunction.card_mul_inner (ClassFunction.restrict ctr.K ψ)
      (trivialClassFunction ↥ctr.K)
    rw [ha] at this
    rw [this]
    simp only [ClassFunction.innerSum, ClassFunction.restrict_apply,
      trivialClassFunction_apply, star_one, mul_one]
  -- `∑_{z:↥K′} ψ(z) = |K′|·⟨Res_{K′} ψ, 1⟩`.
  have hsumK' : (∑ z : ↥ctr.Kprime, ψ (z : G)) = (Nat.card ↥ctr.Kprime : ℂ) * (b : ℂ) := by
    have := ClassFunction.card_mul_inner (ClassFunction.restrict ctr.Kprime ψ)
      (trivialClassFunction ↥ctr.Kprime)
    rw [hb] at this
    rw [this]
    simp only [ClassFunction.innerSum, ClassFunction.restrict_apply,
      trivialClassFunction_apply, star_one, mul_one]
  -- Split the `↥K` sum by membership in `K′` (as a predicate on `↥K`).
  set p : ↥ctr.K → Prop := fun z => (z : G) ∈ ctr.Kprime with hp
  have hsplit : (∑ z : ↥ctr.K, ψ (z : G)) =
      (∑ z ∈ Finset.univ.filter p, ψ (z : G)) +
      (∑ z ∈ Finset.univ.filter (fun z => ¬ p z), ψ (z : G)) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ p (fun z => ψ (z : G))).symm
  -- The `K′`-part (filtered `↥K` sum) reindexes to the `↥K′` sum, via `{z : ↥K // (z:G)∈K′} ≃ ↥K′`.
  have hpart1 : (∑ z ∈ Finset.univ.filter p, ψ (z : G)) =
      ∑ z : ↥ctr.Kprime, ψ (z : G) := by
    -- The bijection `{z : ↥K // (z:G) ∈ K′} ≃ ↥K′`, `⟨⟨z,-⟩, hz⟩ ↦ ⟨z, hz⟩`.
    let φ : {z : ↥ctr.K // p z} ≃ ↥ctr.Kprime :=
      { toFun := fun z => ⟨((z : ↥ctr.K) : G), z.2⟩
        invFun := fun z => ⟨⟨(z : G), hK'K z.2⟩, z.2⟩
        left_inv := fun z => by ext; rfl
        right_inv := fun z => by ext; rfl }
    rw [Finset.sum_subtype (Finset.univ.filter p) (Finset.mem_filter_univ (p := p))
      (fun z => ψ (z : G))]
    exact Fintype.sum_equiv φ (fun z : {z : ↥ctr.K // p z} => ψ ((z : ↥ctr.K) : G))
      (fun z : ↥ctr.Kprime => ψ (z : G)) (fun z => rfl)
  -- The complement-part is constant `= ψ(g)`.
  have hconst' : ∀ z ∈ Finset.univ.filter (fun z : ↥ctr.K => ¬ p z),
      ψ (z : G) = ψ g := by
    intro z hz
    rw [Finset.mem_filter] at hz
    exact hconst (z : G) g z.2 hz.2 hgK hgK'
  set N : ℕ := (Finset.univ.filter (fun z : ↥ctr.K => ¬ p z)).card with hN
  have hpart2 : (∑ z ∈ Finset.univ.filter (fun z : ↥ctr.K => ¬ p z), ψ (z : G))
      = (N : ℂ) * ψ g := by
    rw [Finset.sum_congr rfl hconst', Finset.sum_const, hN, nsmul_eq_mul]
  -- Assemble the identity `|K|·a = |K′|·b + N·ψ(g)`.
  have hident : (Nat.card ↥ctr.K : ℂ) * (a : ℂ) =
      (Nat.card ↥ctr.Kprime : ℂ) * (b : ℂ) + (N : ℂ) * ψ g := by
    have h := hsplit
    rw [hsumK, hpart1, hsumK', hpart2] at h
    exact h
  -- `N ≠ 0`: `g` itself is such an element.
  have hNpos : 0 < N := by
    rw [hN]
    refine Finset.card_pos.mpr ⟨⟨g, hgK⟩, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hgK'⟩
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  -- Solve for `ψ(g)` in `ℂ`.
  have hsolve : ψ g =
      ((Nat.card ↥ctr.K : ℂ) * (a : ℂ) - (Nat.card ↥ctr.Kprime : ℂ) * (b : ℂ)) / (N : ℂ) := by
    rw [eq_div_iff hNne]
    linear_combination -hident
  -- `ψ(g)` is rational (image of a `ℚ`) and an algebraic integer, hence a rational integer.
  obtain ⟨z, hz⟩ := OddOrder.Algebra.exists_int_of_isIntegral_of_mem_range_rat
    (isIntegral_apply_of_mem_ZIrr' hψ g)
    ⟨((Nat.card ↥ctr.K : ℚ) * (a : ℚ) - (Nat.card ↥ctr.Kprime : ℚ) * (b : ℚ)) / (N : ℚ), by
      rw [hsolve]; push_cast; ring⟩
  exact ⟨z, hz.symm⟩

/-- **Peterfalvi (12.16), the (1.10) congruence core**: the cyclotomic-congruence chain of the
(12.16) contradiction.  Given the minimal-counterexample data — a virtual character `ψ ∈ ℤ[Irr G]`,
an order-`p` element `x` and a commuting `g` — together with the facts supplied by the surrounding
§12 machinery (`ψ` constant on the coset, `ψ(xg) = ψ(x)`, by (12.14); `ψ(x) ≡ e (mod 1-ε)`, from the
Dade value relation and (1.10.a) applied to `χ`; and `ψ(g) = mval ∈ ℤ`, by (12.15)), Peterfalvi
(1.10.a) (`exists_integral_apply_sub_of_commute`) and (1.10.b) (`int_dvd_of_one_sub_primRoot_dvd`)
yield `ψ(g) ≡ e (mod p)`, i.e. `p ∣ (mval - e)`.

This isolates the `(1.10)`-using arithmetic of (12.16) (now fully discharged); the remaining
contradiction is the norm/degree inequality (`2e ≤ p+1` of (12.12) together with (12.15)). -/
theorem psi_int_congr_e_mod_p [Finite G] {p : ℕ} (hp : p.Prime) {ε : ℂ}
    (hε : IsPrimitiveRoot ε p) {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G) {x g : G}
    (hx : x ^ p = 1) (hxg : Commute x g) {e mval : ℤ}
    (h_const : ψ (x * g) = ψ x)
    (h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ ψ x - (e : ℂ) = (1 - ε) * w)
    (h_psig_int : ψ g = (mval : ℂ)) :
    (p : ℤ) ∣ (mval - e) := by
  obtain ⟨z, hz, hzeq⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hp.pos hε hψ hx hxg
  obtain ⟨w, hw, hweq⟩ := h_psix
  apply OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd hp hε (hw.sub hz)
  have h1 : ψ x - ψ g = (1 - ε) * z := by rw [← h_const]; exact hzeq
  rw [h_psig_int] at h1
  push_cast
  linear_combination hweq - h1

/-- **Peterfalvi (12.16), the magnitude step**: an integer `mval ≡ e (mod p)` with `1 ≤ e` and
`2e ≤ p+1` (the degree bound (12.12)) satisfies `|mval| ≥ e - 1`.  Indeed the integers `≡ e (mod p)`
nearest `0` are `e` (distance `e`) and `e - p` (distance `p - e ≥ e - 1`, by `2e ≤ p+1`), so every
such value has `|·| ≥ min(e, p-e) ≥ e - 1`. -/
theorem abs_ge_e_sub_one {p : ℕ} (hppos : 0 < p) {e mval : ℤ} (he : 1 ≤ e)
    (h2e : 2 * e ≤ (p : ℤ) + 1) (hdvd : (p : ℤ) ∣ (mval - e)) :
    e - 1 ≤ |mval| := by
  obtain ⟨k, hk⟩ := hdvd
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hppos
  by_cases hk' : 0 ≤ k
  · have hpk : 0 ≤ (p : ℤ) * k := mul_nonneg hpZ.le hk'
    rw [abs_of_nonneg (by omega)]; omega
  · have hk1 : k ≤ -1 := by omega
    have hpk : (p : ℤ) * k ≤ -(p : ℤ) := by nlinarith [mul_le_mul_of_nonneg_left hk1 hpZ.le]
    rw [abs_of_nonpos (by omega)]; omega

/-- **Peterfalvi (12.16), the value-magnitude conclusion**: chaining the `(1.10)` congruence core
(`psi_int_congr_e_mod_p`) with the degree bound `2e ≤ p+1` of (12.12) gives `|ψ(g)| ≥ e - 1` — the
lower bound on `|ψ(g)|` feeding the final norm inequality of (12.16). -/
theorem abs_psi_g_ge_e_sub_one [Finite G] {p : ℕ} (hp : p.Prime) {ε : ℂ}
    (hε : IsPrimitiveRoot ε p) {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G) {x g : G}
    (hx : x ^ p = 1) (hxg : Commute x g) {e mval : ℤ} (he : 1 ≤ e)
    (h2e : 2 * e ≤ (p : ℤ) + 1)
    (h_const : ψ (x * g) = ψ x)
    (h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ ψ x - (e : ℂ) = (1 - ε) * w)
    (h_psig_int : ψ g = (mval : ℂ)) :
    e - 1 ≤ |mval| :=
  abs_ge_e_sub_one hp.pos he h2e
    (psi_int_congr_e_mod_p hp hε hψ hx hxg h_const h_psix h_psig_int)

/-- **Peterfalvi (12.16), the index/degree contradiction** (the heart of the final inequality): the
reduced inequality `(|K| - |K'|)(e-1)² < e·|K|` together with `4·|K'| ≤ |K|` (i.e. `[K:K'] ≥ 4`,
forced by the fixed-point-free order-`p` action of (8.1.c)) and `e ≥ 3` is contradictory.  Indeed
`|K| - |K'| ≥ (3/4)|K|`, so `(3/4)(e-1)² < e`, i.e. `3(e-1)² < 4e`, i.e. `(3e-1)(e-3) < 0` — false
for `e ≥ 3`.  This is the `e/(e-1)² ≤ 3/4 < 1 - |K'|/|K|` step of (12.16). -/
theorem index_ratio_contradiction {e kK kKp : ℝ} (he : 3 ≤ e) (hkKp : 0 < kKp)
    (hidx : 4 * kKp ≤ kK) (hineq : (kK - kKp) * (e - 1) ^ 2 < e * kK) : False := by
  have hkK : 0 < kK := by linarith
  nlinarith [hineq, mul_nonneg (show (0:ℝ) ≤ kK / 4 - kKp by linarith) (sq_nonneg (e - 1)),
    mul_nonneg hkK.le (mul_nonneg (show (0:ℝ) ≤ e - 3 by linarith)
      (show (0:ℝ) ≤ 3 * e - 1 by linarith))]

/-- **Peterfalvi (12.16), the (12.11) reduction**: the final norm inequality
`((|K|-|K'|)/|M|)(e-1)² + 1 - e/|H| < 1` together with `|M| ≤ |K|·|H|` of (12.11) reduces to
`(|K|-|K'|)(e-1)² < e·|K|` (clear `|M|`, `|H|`, then bound `|M|` above). -/
theorem norm_ineq_reduce {e kK kKp kM kH : ℝ} (hkM : 0 < kM) (hkH : 0 < kH)
    (he1 : 0 ≤ e) (hM : kM ≤ kK * kH)
    (hnorm : ((kK - kKp) / kM) * (e - 1) ^ 2 + 1 - e / kH < 1) :
    (kK - kKp) * (e - 1) ^ 2 < e * kK := by
  have h1 : (kK - kKp) * (e - 1) ^ 2 / kM < e / kH := by
    have e1 : (kK - kKp) * (e - 1) ^ 2 / kM = ((kK - kKp) / kM) * (e - 1) ^ 2 := by ring
    rw [e1]; linarith [hnorm]
  rw [div_lt_div_iff₀ hkM hkH] at h1
  have h2 : e * kM ≤ e * (kK * kH) := mul_le_mul_of_nonneg_left hM he1
  have h3 : (kK - kKp) * (e - 1) ^ 2 * kH < e * kK * kH := by nlinarith [h1, h2]
  exact lt_of_mul_lt_mul_right h3 hkH.le

/-- **Peterfalvi (12.16), the closing contradiction** (norm-inequality endgame): given the final
norm bound `((|K|-|K'|)/|M|)(e-1)² + 1 - e/|H| < 1` (from (7.3)/(7.8.b)/(8.17) with `|ψ(g)| ≥ e-1`),
the index bound `|M| ≤ |K|·|H|` of (12.11), the degree bound `e ≥ 3`, and the fixed-point-free
`[K:K'] ≥ 4` of (8.1.c), the minimal counterexample is impossible.  Combines `norm_ineq_reduce`
with `index_ratio_contradiction`. -/
theorem counterexample_closing {e kK kKp kM kH : ℝ} (he : 3 ≤ e) (hkKp : 0 < kKp)
    (hkM : 0 < kM) (hkH : 0 < kH) (hidx : 4 * kKp ≤ kK) (hM : kM ≤ kK * kH)
    (hnorm : ((kK - kKp) / kM) * (e - 1) ^ 2 + 1 - e / kH < 1) : False :=
  index_ratio_contradiction he hkKp hidx (norm_ineq_reduce hkM hkH (by linarith) hM hnorm)

/-- **Peterfalvi (12.16), the middle (norm-bound) glue**: from `|ψ(g)| ≥ e-1` and the three §7/§8
norm bounds — `A`: `‖ψ^{ρM}‖² ≥ (|K-K'|/|M|)|ψ(g)|²` (from (12.15)), `B`: `‖ψ^ρ‖² ≥ 1 - e/|H|`
((7.8.b)), `C`: `‖ψ^{ρM}‖² + ‖ψ^ρ‖² < 1` ((7.3) with (8.17)) — the norm conclusion
`(|K-K'|/|M|)(e-1)² + 1 - e/|H| < 1` follows (`|ψ(g)|² = mval² ≥ (e-1)²`, then linear). -/
theorem norm_conclusion_glue {e mval : ℤ} {kK kKp kM kH normRhoM normRho : ℝ}
    (he : 3 ≤ e) (hkKp : 0 < kKp) (hkM : 0 < kM) (hidx : 4 * kKp ≤ kK)
    (hmag : (e : ℝ) - 1 ≤ |(mval : ℝ)|)
    (hA : (kK - kKp) / kM * (mval : ℝ) ^ 2 ≤ normRhoM)
    (hB : (1 : ℝ) - (e : ℝ) / kH ≤ normRho)
    (hC : normRhoM + normRho < 1) :
    (kK - kKp) / kM * ((e : ℝ) - 1) ^ 2 + 1 - (e : ℝ) / kH < 1 := by
  have hsq : ((e : ℝ) - 1) ^ 2 ≤ (mval : ℝ) ^ 2 := by
    have heR : (3 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    nlinarith [hmag, sq_abs (mval : ℝ), abs_nonneg (mval : ℝ)]
  have hpos : 0 ≤ (kK - kKp) / kM := div_nonneg (by linarith) hkM.le
  have hA' : (kK - kKp) / kM * ((e : ℝ) - 1) ^ 2 ≤ normRhoM :=
    le_trans (mul_le_mul_of_nonneg_left hsq hpos) hA
  linarith [hA', hB, hC]

/-- **Peterfalvi (12.16), the full assembly** (the entire argument, parameterized on its gated
upstream): the minimal counterexample is impossible.  Combines the `(1.10)` congruence/magnitude
start (`abs_psi_g_ge_e_sub_one`: `|ψ(g)| ≥ e-1`), the §7/§8 norm-bound middle (`norm_conclusion_glue`
from the three bounds `hA`/`hB`/`hC`), and the index/degree endgame (`counterexample_closing`).

Every hypothesis is a fact supplied by §7/§8/§12: `h_const` = (12.14), `h_psix` = Dade value relation
with (1.10.a) on `χ`, `h_psig_int` = (12.15), `h2e` = (12.12); `hA` = (12.15)+`|ψ(g)|`, `hB` = (7.8.b),
`hC` = (7.3)+(8.17); `hM` = (12.11), `hidx` = fpf `[K:K'] ≥ 4` of (8.1.c).  The remaining work to close
`counterexample_contradiction` is exactly the construction of these — the §7 `ρ`/`ρM` machinery. -/
theorem counterexample_contradiction_of_facts [Finite G]
    {p : ℕ} (hp : p.Prime) {ε : ℂ} (hε : IsPrimitiveRoot ε p)
    {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G) {x g : G} (hx : x ^ p = 1) (hxg : Commute x g)
    {e mval : ℤ} (he : 3 ≤ e) (h2e : 2 * e ≤ (p : ℤ) + 1)
    (h_const : ψ (x * g) = ψ x)
    (h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ ψ x - (e : ℂ) = (1 - ε) * w)
    (h_psig_int : ψ g = (mval : ℂ))
    {kK kKp kM kH normRhoM normRho : ℝ}
    (hkKp : 0 < kKp) (hkM : 0 < kM) (hkH : 0 < kH)
    (hidx : 4 * kKp ≤ kK) (hM : kM ≤ kK * kH)
    (hA : (kK - kKp) / kM * (mval : ℝ) ^ 2 ≤ normRhoM)
    (hB : (1 : ℝ) - (e : ℝ) / kH ≤ normRho)
    (hC : normRhoM + normRho < 1) :
    False := by
  have hmagZ : (e - 1 : ℤ) ≤ |mval| :=
    abs_psi_g_ge_e_sub_one hp hε hψ hx hxg (by linarith) h2e h_const h_psix h_psig_int
  have hmag : (e : ℝ) - 1 ≤ |(mval : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hmagZ
  have heR : (3 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  exact counterexample_closing heR hkKp hkM hkH hidx hM
    (norm_conclusion_glue he hkKp hkM hidx hmag hA hB hC)

/-- **Peterfalvi (12.12) → (12.16) numerical bridge**: the (12.12) conclusion `e ∣ p+1` together
with `e` odd (odd order) gives the bound `2e ≤ p+1` cited by (12.16).  Since `p` is odd, `2 ∣ p+1`;
as `gcd(2,e)=1`, `2e ∣ p+1`, hence `2e ≤ p+1`.  (`e ≤ (p+1)/2` in the textbook.) -/
theorem two_mul_le_succ_of_odd_dvd {e p : ℕ} (hp : Odd p) (he : Odd e)
    (hdvd : e ∣ (p + 1)) : 2 * e ≤ p + 1 :=
  Nat.le_of_dvd (by omega) (he.coprime_two_left.mul_dvd_of_dvd_of_dvd (hp.add_one).two_dvd hdvd)

/-- **Peterfalvi (8.1.c) → (12.16) numerical bridge**: a fixed-point-free order-`p` action on
`K/K'` forces `p ∣ ([K:K'] - 1)`; with `[K:K'] > 1` and `p ≥ 3` this gives `[K:K'] ≥ 4`, the index
bound contradicting `[K:K'] < 4` in the (12.16) endgame. -/
theorem four_le_of_dvd_sub_one {p n : ℕ} (hp : 3 ≤ p) (hn : 1 < n) (hdvd : p ∣ (n - 1)) :
    4 ≤ n := by
  have : p ≤ n - 1 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- **Peterfalvi (12.9), the centralizer witness extraction**: the rank-two witness datum records
`¬(C_G(x) ⊓ K ≤ K')`, which directly yields an element `g ∈ C_K(x)` with `g ∉ K'` — the `g`
commuting with `x` used throughout the (12.16) argument.  (Pure `SetLike` extraction, ungated.) -/
theorem exists_witness_g {ctr : CounterexampleHypothesis (G := G)}
    (witness : RankTwoWitnessData ctr) :
    ∃ g : G, Commute witness.x g ∧ g ∈ ctr.K ∧ g ∉ ctr.Kprime := by
  obtain ⟨g, hgA, hgB⟩ := SetLike.not_le_iff_exists.mp witness.CKx_not_le_Kprime
  rw [Subgroup.mem_inf] at hgA
  exact ⟨g, Subgroup.mem_centralizer_iff.mp hgA.1 witness.x (Set.mem_singleton _), hgA.2, hgB⟩

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


open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8)/(12.16), the witness `Hypothesis78`**: the second maximal subgroup `L` of
(12.9) carries the full §7 (7.8) structure — the `ρ`-machinery `Hypothesis71`, the distinguished
induced family `{ζ_i = Ind θ_i}`, the coherent extension `ν`, and the (7.8.a) coherence agreement.

Assembles `hypothesis78OfDade` from three genuine ingredients for the witness `L`:
* the (12.6) coherence `witness_L_coherent` supplies the extension `ν = coh.extension`, whose
  `IsCoherent.extension_inner_eq`/`extends_on_supported` give the `nu_isometry` (via
  `coherence_extension_inner_eq_on_family`) and the (7.8.a) agreement (via
  `coherence_hagree_dadeMap`);
* the placed family `exists_witness_placed_family` supplies the `Fin (n+1)`-indexed `θ` with the
  distinguished character at index `0` (`Ind (θ 0)(1) = [L:H] = e`) and the trivial character `1_H`
  at `ind1H ≠ 0`, injective and covering;
* the (12.1) support `A(L) = H#` (`typeIA_eq_sharp`) and the degree coefficients `d_i = θ_i(1)`
  (`induce_apply_one`), with the difference support `ψ_i = ζ_i − d_i ζ_0 ⊆ H#` from
  `induce_diff_support`.

This is the (7.8) hypothesis to which Peterfalvi's (7.8.b) norm bound `hB` of
`CounterexampleDadeData` applies (via `zetaNuRhoNormSqGeOfDade`). -/
theorem witness_L_hypothesis78 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L,
      Nonempty (OddOrder.Peterfalvi.S09.Hypothesis78 G (typeIA data.L hyp.typeI) data.L) := by
  classical
  obtain ⟨hyp, ⟨coh⟩⟩ := witness_L_coherent hG data
  refine ⟨hyp, ?_⟩
  have hHL : hyp.typeI.typeF.H ≤ data.L := hyp.typeI.typeF.H_le
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf data.L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal data.L
  -- (12.1): the type-I support `A(L)` is `H#`.
  have hAH : typeIA data.L hyp.typeI = (hyp.typeI.typeF.H : Set G) \ {1} :=
    witness_typeIA_eq_sharp hG data hyp
  -- `H = L_F` is `L`-conjugation invariant (from the `subgroupOf`-normality).
  have hHnorm : ∀ (l : ↥data.L) {h : G}, h ∈ hyp.typeI.typeF.H →
      (l : G) * h * (l : G)⁻¹ ∈ hyp.typeI.typeF.H := by
    intro l h hh
    have hhL : h ∈ data.L := hHL hh
    have hmem : (⟨h, hhL⟩ : ↥data.L) ∈ (hyp.typeI.typeF.H).subgroupOf data.L :=
      (Subgroup.mem_subgroupOf).mpr hh
    have hconj := hKnormal.conj_mem ⟨h, hhL⟩ hmem l
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  -- The placed induced family for `L`.
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ := exists_witness_placed_family hyp
  -- Every non-trivial member `Ind θ_i` (`i ≠ ind1H`) lies in the coherent family `S`.
  have hSmem : ∀ i, i ≠ ind1H →
      ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)
        ∈ hyp.Sset := by
    intro i hi
    refine ⟨θ i, fun htriv_i => hi (hinj ?_), rfl⟩
    change ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ ind1H : ClassFunction _ ℂ)
    rw [htriv_i, htriv]
  -- Degree coefficients `d_i = θ_i(1)`.
  let d : Fin (n + 1) → ℂ :=
    fun i => (θ i : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L) ℂ)
      (1 : ↥((hyp.typeI.typeF.H).subgroupOf data.L))
  have hd : ∀ i, d i = (θ i : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L) ℂ)
      (1 : ↥((hyp.typeI.typeF.H).subgroupOf data.L)) := fun _ => rfl
  -- `ζ_i(1) = d_i · ζ_0(1)`.
  have hdeg : ∀ i, ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ) (1 : ↥data.L)
      = d i * ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥data.L) := by
    intro i
    rw [ClassFunction.induce_apply_one ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ i : ClassFunction _ ℂ), hdeg0, hd i]
    ring
  -- `ζ_0(1) = ζ_{ind1H}(1)` (both `[L:H]`).
  have hdeg_match : ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ 0 : ClassFunction _ ℂ) (1 : ↥data.L)
      = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
        (θ ind1H : ClassFunction _ ℂ) (1 : ↥data.L) := by
    rw [hdeg0, htriv]
    change (((hyp.typeI.typeF.H).subgroupOf data.L).index : ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L)
          (trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf data.L)) (1 : ↥data.L)
    rw [induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)]
  -- `ψ_i = ζ_i − d_i ζ_0` is supported on `A(L) = H#`.
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
  -- Assemble the `Hypothesis78` via `hypothesis78OfDade`.
  refine ⟨hypothesis78OfDade hyp.toHypothesis71
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeIsometry
    hyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv hdeg_match
    coh.extension ?_ ?_⟩
  · -- `nu_isometry`: the coherent extension is isometric on the family members.
    intro i j hi hj
    exact coherence_extension_inner_eq_on_family coh (hSmem i hi) (hSmem j hj)
  · -- `hagree`: the (7.8.a) coherence agreement `τ ψ_i = ν ζ_i − d_i ν ζ_0`.
    intro i _ hi_ind
    obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ i)
    exact coherence_hagree_dadeMap hyp.dadeData.dade hyp.hconj coh
      (hSmem i hi_ind) (hSmem 0 (Ne.symm hind1H)) (m0 := 1) (mi := deg_i) (by norm_num)
      (by rw [hd i, hdeg_i_eq, Nat.cast_one, div_one]) (psi_support i)


/-- **Peterfalvi (7.8.b)/(12.12) size condition for an odd-order Frobenius group**: if a finite
Frobenius group has kernel `N` and complement `A` both of **odd** order, with `N ≠ ⊥`, then
`2|A| + 1 ≤ |N|` (equivalently `e ≤ (h-1)/2`, the `smallIndex` hypothesis of the §7 `(7.8.b)` norm
bound).  The complement `A` acts freely on `N#`, so `|A| ∣ |N| - 1` (`card_kernel_modEq_one`,
Isaacs 6.1); as `|N|` is odd, `|N| - 1` is even, and an odd divisor of an even number is at most
half of it, so `|N| - 1 ≥ 2|A|`.  This is the `2e_i + 1 ≤ h_i` shape consumed by
`localSmallIndex_of_family_cardinalities` for the witness `L` of (12.16).  (General Frobenius fact,
hoistable to `Ch06`.) -/
theorem frobenius_two_mul_card_complement_add_one_le_card_kernel {Γ : Type*} [Group Γ] [Finite Γ]
    {N A : Subgroup Γ} (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup Γ N A)
    (hNodd : Odd (Nat.card ↥N)) (hAodd : Odd (Nat.card ↥A)) (hNnt : N ≠ ⊥) :
    2 * Nat.card ↥A + 1 ≤ Nat.card ↥N := by
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNnt
  have hN1 : 1 < Nat.card ↥N := Finite.one_lt_card
  -- `|A| ∣ |N| - 1` from `|N| ≡ 1 [MOD |A|]` (Isaacs 6.1).
  obtain ⟨m, hm⟩ : Nat.card ↥A ∣ Nat.card ↥N - 1 :=
    (Nat.modEq_iff_dvd' hN1.le).mp hFrob.card_kernel_modEq_one.symm
  -- `|N| - 1` is even (`|N|` odd), `|A|` is odd, so the cofactor `m` is even.
  have hNm1_even : Even (Nat.card ↥N - 1) := Nat.Odd.sub_odd hNodd odd_one
  have hm_even : Even m := by
    rcases (Nat.even_mul.mp (hm ▸ hNm1_even)) with hA | hm
    · exact absurd hA (Nat.not_even_iff_odd.mpr hAodd)
    · exact hm
  -- `m ≠ 0` (else `|N| = 1`), so `m ≥ 2`; hence `|N| - 1 = |A|·m ≥ 2|A|`.
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · rw [h0, Nat.mul_zero] at hm; omega
    · exact hp
  have hm2 : 2 ≤ m := Nat.le_of_dvd hm_pos hm_even.two_dvd
  have hge : Nat.card ↥A * 2 ≤ Nat.card ↥A * m := Nat.mul_le_mul_left _ hm2
  omega

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8.b)/(12.16) `hB` for the witness `L`**: the second maximal subgroup `L` of
(12.9) satisfies the `(7.8.b)` norm lower bound `1 − e/h ≤ ‖ζ_0^{νρ}‖²`
(`= CounterexampleDadeData.hB`), where `e = [L:H]` (`complementIndex`), `h = |H|` (`kernelOrder`),
`ζ_0 = Ind θ_0` the distinguished coherent-family member.  Assembles the witness `Hypothesis78`
(as in `witness_L_hypothesis78`) and feeds the concrete §7 producer `zetaNuRhoNormSqGeOfDade`,
supplying its four genuine `(7.8)` inputs: `hzeta0nu` (`ζ_0^ν ⊥ 1_G`, `witness_L_hzeta0nu`),
`hζ0norm` (`‖ζ_0‖² = 1`, Frobenius), `a`/`ha` (`(β, ζ_0^ν) + 1 ∈ ℤ`, `exists_betaDecomp_a`), and
`hsmall` (`2e + 1 ≤ h`, `frobenius_two_mul_card_complement_add_one_le_card_kernel`).  This realizes
the §7 hard-floor consumption for (12.16): the (7.8.b) `hB` field is now constructible. -/
theorem witness_L_zeta_bound [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L,
      ∃ H78 : OddOrder.Peterfalvi.S09.Hypothesis78 G (typeIA data.L hyp.typeI) data.L,
        (1 : ℝ) - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ) ≤ H78.zetaNuRhoNormSq := by
  classical
  obtain ⟨hyp, C, hC, hNonTI⟩ := witness_L_hypothesis_frobenius hG data
  -- The witness dispatches only through (12.6) cases (b)/(c) (`H^#` non-TI), never case (a).
  obtain ⟨coh⟩ : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A) := by
    rcases hyp.typeI.alternative with hTI | hab | hexp
    · exact absurd hTI hNonTI
    · exact frobenius_typeI_coherent_of_abelianKernel hG hyp ⟨C, hC⟩ hab
    · exact frobenius_typeI_coherent_of_cyclicQuotient hG hyp ⟨C, hC⟩ hexp
  have hHL : hyp.typeI.typeF.H ≤ data.L := hyp.typeI.typeF.H_le
  haveI hKnormal : ((hyp.typeI.typeF.H).subgroupOf data.L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal data.L
  -- `hC`'s kernel is written with the `hyp.H` accessor; register the normality in that form too.
  haveI : (hyp.H.subgroupOf data.L).Normal := hKnormal
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
  obtain ⟨n, θ, ind1H, hind1H, hdeg0, htriv, hinj, hcover⟩ := exists_witness_placed_family hyp
  have hSmem : ∀ i, i ≠ ind1H →
      ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)
        ∈ hyp.Sset := by
    intro i hi
    refine ⟨θ i, fun htriv_i => hi (hinj ?_), rfl⟩
    change ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ i : ClassFunction _ ℂ)
        = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf data.L) (θ ind1H : ClassFunction _ ℂ)
    rw [htriv_i, htriv]
  -- `θ_0 ≠ 1` (else `θ_0 = θ_{ind1H}` by `htriv`, so `0 = ind1H` by `hinj`, contra `hind1H`).
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
  -- The concrete witness `Hypothesis78`.
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
  have hCodd : Odd (Nat.card ↥C) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card C)
  have hKcard : Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L) = Nat.card hyp.typeI.typeF.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  have hKnt : ((hyp.typeI.typeF.H).subgroupOf data.L) ≠ ⊥ := by
    haveI : Nontrivial ↥hyp.typeI.typeF.H :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hyp.typeI.typeF.H_nontrivial
    haveI : Nontrivial ↥((hyp.typeI.typeF.H).subgroupOf data.L) :=
      (Subgroup.subgroupOfEquivOfLe hHL).toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  have hcompl : Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L) * Nat.card ↥C
      = Nat.card ↥data.L := hC.isComplement.card_mul_card
  have hsmall : H78.smallIndex := by
    have hfrob := frobenius_two_mul_card_complement_add_one_le_card_kernel hC hKodd hCodd hKnt
    show 2 * H78.complementIndex + 1 ≤ H78.kernelOrder
    have hke : H78.kernelOrder = Nat.card ↥((hyp.typeI.typeF.H).subgroupOf data.L) := by
      rw [hKcard]; rfl
    have hce : H78.complementIndex = Nat.card ↥C := by
      show Nat.card ↥data.L / Nat.card hyp.typeI.typeF.H = Nat.card ↥C
      rw [← hKcard, ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
    rw [hke, hce]; exact hfrob
  refine ⟨hyp, H78, ?_⟩
  exact zetaNuRhoNormSqGeOfDade hyp.toHypothesis71
    (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj).toDadeIsometryData.isDadeIsometry
    hyp.typeI.typeF.H hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv hdeg_match
    coh.extension hnu_isometry hagree
    (witness_L_hzeta0nu hG hyp hC coh hAH (θ 0) hθ0_ne)
    (inner_self_induce_eq_one_of_frobeniusGroup hC (θ 0) hθ0_ne) a ha hsmall


/-! ## (12.17): forcing case (b) of Theorem (8.8) — the all-type-I non-existence argument

Peterfalvi (12.17) shows that case (a) of Theorem (8.8) — *every* maximal subgroup of `G` being of
type I — is impossible.  The argument assembles the type-I maximals into a Frobenius family in the
sense of (7.10) (`S09.FrobeniusFamily`) and derives the contradiction from (7.11)
(`S09.not_trivial_G0`).  Combined with the (8.8) dichotomy (`theorem88_dichotomy`, BG §16), this
forces the case-(b) pairing data `Theorem88CaseBData`, which the Feit–Thompson endgame consumes.

The genuinely group-theoretic content of the family — the Frobenius structure (from (12.7)) and the
self-normalizing identity `L = N_G(L_F)` — is proved here.  The remaining §8/§10 covering inputs
(TI sharp-sets via (8.13.c1), coprime kernels and the `G#` cover via (8.17)) are isolated in the
faithful carrier `TypeICovering`. -/

section Theorem1217

variable [Finite G]

/-! The normalizer bridge `maximalSubgroup_eq_normalizer_maxNilpotentNormalHall` (`L = N_G(L_F)`
for maximal `L` with `L_F ≠ ⊥`) now lives with the (8.6.a)/(8.16) centralizer-containment block
before (12.10), where the type-`P` pins consume it. -/

/-- **Peterfalvi (8.13.c1)+(2.3), all-type-I case** — the escaping-centralizer control that makes
each type-I kernel's Fitting subgroup a `TI`-subgroup, supplying the `FittingIsTI` gate of the
(12.17) `isTI` covering input.

For a maximal subgroup `M` of a minimal simple group of odd order in which **every** maximal subgroup
is of type I (`hall`), the Fitting subgroup `F(M)` is `TI` (`S15.FittingIsTI M`).  In the all-type-I
configuration the (8.13.c1) escaping-centralizer control forces `R(x) = 1` on `M_σ#` (the (8.14)
signalizer is trivial), so `M_σ = M_F = F(M)` is a genuine trivial-intersection subgroup.

**Genuinely still-missing**: the (8.13.c1) escaping-centralizer control is `escapingCentralizers_control`
(S10:526), itself an open BG §16 / (2.3) residual, and the passage from it to `FittingIsTI` is not
assembled anywhere in reach of `S14`.  BG §16 exposes `FittingIsTI` only in the `M_F ≠ M_σ` /
type-`P₂` directions (`fittingIsTI_of_isTypeP2`, `fitting_isTI_of_mf_ne_msigma`), never for the
all-type-I `M_F = M_σ` case, which is exactly the escaping-centralizer content here.

**Soundness**: the statement is TRUE and **not** a false general implication.  It is *not* claimed
for an arbitrary type-I subgroup — the (12.10)/(12.16) Frobenius witness `L` is type-I-like yet
has `H^# = (L_F)#` **not** `TI` in `G` (Pf (12.10), see `sibleyTarget_frobI`), so the conclusion
genuinely requires the ambient all-type-I hypothesis `hall` (which excludes the counterexample
configuration and puts us in the (8.17.a) type-I covering case where (8.13.c1) applies).  Tied to
`hG`, `M` maximal, its type-I witness, and `hall`. -/
private theorem allTypeI_fittingIsTI (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (_hI : IsTypeI M)
    (_hall : ∀ N : Subgroup G, N ∈ maximalSubgroups G → IsTypeI N) :
    OddOrder.BG.Ch4.S15.FittingIsTI M := by
  sorry

/-- **Peterfalvi (8.8.a) dichotomy, all-type-I case** — the case-(b) covering branch of BG Theorem
E cannot occur when every maximal subgroup is of type I.

If `data`'s cover admits a `BGTheoremENonTypeICovering` (the two-exceptional-subgroup case (8.8.b)
of BG Theorem E) while every maximal subgroup is of type I (`hall`), a contradiction results.

**Genuinely still-missing**: the `BGTheoremENonTypeICovering` carrier records only the exceptional
`Ẑ`-set and its cover geometry — it does **not** expose the type-`P` maximal whose Theorem 14.7
duality produced `Ẑ` (see `nonTypeICovering_of_isTypeP`, whose inputs `Mref, Kref, …` are consumed
but not re-exported).  So no non-type-I maximal is directly extractable from `hNonTypeI` to
contradict `hall`.  The (8.8) dichotomy's *exclusivity* — case (b) selected `iff` some maximal is
non-type-I — is the BG §16 (8.8.a) residual (parallel to `theorem88_dichotomy`), not assembled in
reach of `S14`.

**Soundness**: the statement is TRUE — the (8.8.b) covering branch is produced (in
`nonTypeICovering_of_isTypeP`) *only* from a type-`P` (= non-type-I, `isTypeNonI_of_isTypeP`)
maximal, which `hall` forbids; so the two hypotheses are jointly contradictory.  It is **not** a
false general implication: it does not claim `BGTheoremENonTypeICovering` is empty unconditionally
(it is inhabited whenever a non-type-I maximal exists) — only its incompatibility with the
all-type-I hypothesis `hall`.  Tied to `hG`, the specific `data`, its non-type-I covering, and
`hall`. -/
private theorem not_nonTypeICovering_of_all_typeI (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {data : OddOrder.Peterfalvi.S10.BGTheoremECoverData G}
    (_hcov : OddOrder.Peterfalvi.S10.BGTheoremENonTypeICovering data)
    (_hall : ∀ N : Subgroup G, N ∈ maximalSubgroups G → IsTypeI N) :
    False := by
  sorry

/-- **§8/§10 covering inputs to Peterfalvi (12.17)** — the all-type-I case of Theorem (8.8).

When every maximal subgroup of `G` is of type I, the §8 covering theory (BG Theorem E, (8.17), and
the escaping-centralizer control (8.13.c1)) supplies a finite family of conjugacy-class
representatives `reps i` whose maximal nilpotent normal Hall subgroups `(reps i)_F`:
* number at least two (`two_le`);
* have TI sharp-sets `((reps i)_F)#` (`isTI`, via (8.13.c1)+(2.3));
* are pairwise of coprime order (`coprime`, via the (8.17) prime partition);
* cover `G#` up to conjugacy (`covers`, the (8.17.a) type-I covering).

These are exactly the inputs the (12.17) argument feeds to (7.11), beyond the genuinely
group-theoretic family facts (Frobenius structure, `reps i = N_G((reps i)_F)`) discharged in
`not_all_maximal_typeI`. -/
structure TypeICovering (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) where
  /-- Number of conjugacy classes of maximal subgroups. -/
  k : ℕ
  /-- Conjugacy-class representatives of the maximal subgroups. -/
  reps : Fin k → Subgroup G
  /-- Each representative is maximal. -/
  reps_maximal : ∀ i, reps i ∈ maximalSubgroups G
  /-- (7.10): at least two members. -/
  two_le : 2 ≤ k
  /-- (8.13.c1)+(2.3): each kernel sharp-set is a TI-subset. -/
  isTI : ∀ i, IsTISubset ((maxNilpotentNormalHall (reps i) : Set G) \ {1}) (reps i)
  /-- (8.17): the kernels have pairwise-coprime order. -/
  coprime : ∀ ⦃i j⦄, i ≠ j →
    Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall (reps i)))
      (Nat.card ↥(maxNilpotentNormalHall (reps j)))
  /-- (8.17.a): the conjugates of the kernels cover every nonidentity element. -/
  covers : ∀ x : G, x ≠ 1 →
    ∃ i, ∃ g : G, g * x * g⁻¹ ∈ (maxNilpotentNormalHall (reps i) : Set G) \ {1}


/-- **Peterfalvi (8.17)/(8.13.c1), all-type-I case**: the §8 covering inputs of (12.17) exist.

Built as an honest reduction from BG Theorem E (`S10.bgTheoremE_cover_data`): in the all-type-I case
every representative `M_i` has `data.tau i = .I` (type exclusivity, `not_isTypeI_of_isTypeNonI`), so
`mainSubgroup (M_i) (τ_i) = (M_i)_F`.  The `reps`/`reps_maximal` plumbing, `coprime` (the (8.17)
prime-factor partition is disjoint, hence the kernels are coprime), `two_le` (a single class would
make `|G#| = (|M_s|-1)|G:M| < |G|-1 = |G#|`), and `covers` (the thickened cover lands in
`(M_i)_F`-conjugates, `thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall`) are all
discharged.  Two upstream facts remain isolated as residual sorries: `isTI`, the escaping-centralizer
control (8.13.c1)+(2.3) making each kernel sharp-set a TI-subset; and the selection of the type-I
cover branch under `hall`, the (8.8.a) dichotomy (BG §16, parallel to `theorem88_dichotomy`). -/
theorem exists_typeICovering (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) :
    Nonempty (TypeICovering hG hall) := by
  classical
  -- `BGTheoremECoverData.ι : Type*` is universe-polymorphic; pin the index type to `Type 0`.
  obtain ⟨data, hcover⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  haveI : Fintype data.ι := data.finite_index
  -- **Every representative is type I**, so `data.tau i = .I` and hence
  -- `mainSubgroup (M_i) (τ_i) = (M_i)_F`.  Type exclusivity is
  -- `not_isTypeI_of_isTypeNonI` (BG §16): a type-`P` (= non-type-I) maximal is not type I.
  have hMF : ∀ i, mainSubgroup (data.reps i) (data.tau i)
      = maxNilpotentNormalHall (data.reps i) := by
    intro i
    have hI : IsTypeI (data.reps i) := hall _ (data.maximal i)
    have htau := data.typed i
    have htauI : data.tau i = PeterfalviType.I := by
      by_contra hne
      have hNonI : IsTypeNonI (data.reps i) := by
        cases hc : data.tau i with
        | I => exact absurd hc hne
        | II => rw [hc] at htau; exact Or.inl htau
        | III => rw [hc] at htau; exact Or.inr (Or.inl htau)
        | IV => rw [hc] at htau; exact Or.inr (Or.inr (Or.inl htau))
        | V => rw [hc] at htau; exact Or.inr (Or.inr (Or.inr htau))
      exact OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG (data.maximal i) hNonI hI
    simp only [htauI, mainSubgroup]
  -- The `Fin k`-indexing of the representatives (`e : data.ι ≃ Fin k`).
  set e := Fintype.equivFin data.ι with he
  rcases hcover with hTypeI | hNonTypeI
  · -- **(8.8.a) type-I cover branch.**
    refine ⟨{
      k := Fintype.card data.ι
      reps := fun j => data.reps (e.symm j)
      reps_maximal := fun j => data.maximal (e.symm j)
      two_le := ?_
      isTI := ?_
      coprime := ?_
      covers := ?_ }⟩
    · -- **`two_le`** (discharged): at least two conjugacy classes of maximal subgroups (7.10).
      -- A single class would force `|G#| = |thickenedA1(M)| = (|M_s| - 1)|G : M|`; but
      -- `(|M_s| - 1)|G : M| ≤ (|M| - 1)|G : M| = |G| - |G : M| ≤ |G| - 2 < |G| - 1 = |G#|`, and an
      -- empty class would force `|G#| = 0`, both impossible.  No counting of disjoint unions is
      -- needed: a one-element index makes the cover `⋃ᵢ thickenedA1(Mᵢ)` equal to a single
      -- `thickenedA1(M)`, whose cardinality is strictly below `|G#|`.
      haveI : Nontrivial G := hG.simple.toNontrivial
      by_contra hlt
      rw [Nat.not_le] at hlt
      have hcard01 : Fintype.card data.ι = 0 ∨ Fintype.card data.ι = 1 := by omega
      rcases hcard01 with h0 | h1
      · -- empty index: the cover is empty, but `G#` contains a nonidentity element.
        rw [Fintype.card_eq_zero_iff] at h0
        have hempty : (⋃ i, data.cover i) = ∅ :=
          Set.iUnion_of_empty _
        rw [← hTypeI.cover_nonidentity] at hempty
        obtain ⟨b, hb⟩ := exists_ne (1 : G)
        have hbmem : b ∈ sharpSubgroup (⊤ : Subgroup G) := by
          simp only [sharpSubgroup, Subgroup.coe_top, Set.mem_sdiff, Set.mem_univ, true_and,
            Set.mem_singleton_iff]
          exact hb
        rw [hempty] at hbmem
        exact hbmem.elim
      · -- one class: `⋃ᵢ thickenedA1(Mᵢ) = thickenedA1(M)`, of cardinality `< |G#|`.
        obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp h1
        have hunion : (⋃ i, data.cover i) = data.cover i₀ := by
          ext x
          simp only [Set.mem_iUnion]
          exact ⟨fun ⟨i, hi⟩ => by rwa [hi₀ i] at hi, fun hx => ⟨i₀, hx⟩⟩
        rw [← hTypeI.cover_nonidentity] at hunion
        have hcard_eq : Nat.card ↥(data.cover i₀) = Nat.card G - 1 := by
          rw [Nat.card_coe_set_eq, ← hunion]
          show ((↑(⊤ : Subgroup G) : Set G) \ {1}).ncard = Nat.card G - 1
          rw [Subgroup.coe_top, Set.ncard_diff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ]
        rw [data.cover_card i₀] at hcard_eq
        -- Arithmetic contradiction.
        have hmain_le : mainSubgroup (data.reps i₀) (data.tau i₀) ≤ data.reps i₀ :=
          (hMF i₀).le.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le (data.reps i₀))
        have ham : Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀))
            ≤ Nat.card ↥(data.reps i₀) := Subgroup.card_le_of_le hmain_le
        have hidx0 : (data.reps i₀).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have hidx1 : (data.reps i₀).index ≠ 1 :=
          fun h => (data.maximal i₀).1 (Subgroup.index_eq_one.mp h)
        have hidx : 2 ≤ (data.reps i₀).index := by omega
        have hmidx : Nat.card ↥(data.reps i₀) * (data.reps i₀).index = Nat.card G :=
          Subgroup.card_mul_index (data.reps i₀)
        have hm_pos : 0 < Nat.card ↥(data.reps i₀) := Nat.card_pos
        have hG2 : 2 ≤ Nat.card G :=
          le_trans hidx (hmidx ▸ Nat.le_mul_of_pos_left (data.reps i₀).index hm_pos)
        have hb1 : (Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀)) - 1)
            * (data.reps i₀).index
            ≤ (Nat.card ↥(data.reps i₀) - 1) * (data.reps i₀).index :=
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_right ham 1)
        have hrhs : (Nat.card ↥(data.reps i₀) - 1) * (data.reps i₀).index
            = Nat.card G - (data.reps i₀).index := by rw [Nat.sub_one_mul, hmidx]
        rw [hrhs] at hb1
        -- `hcard_eq : P = |G| - 1`, `hb1 : P ≤ |G| - idx`, `idx ≥ 2`, `|G| ≥ 2` ⟹ `False`.
        set P := (Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀)) - 1)
          * (data.reps i₀).index with hP
        omega
    · -- `isTI`: each kernel sharp-set `((M_i)_F)#` is a TI-subset, by (8.13.c1)+(2.3).
      -- Honest derivation: `FittingIsTI (M_j)` (the (8.13.c1) escaping-centralizer gate,
      -- `allTypeI_fittingIsTI`) feeds `maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`
      -- (S16, `M_F# TI` with normalizer `N_G(M_F)`); and `N_G(M_F) = M_j` for the type-I maximal
      -- (`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`, kernel `≠ ⊥`).
      intro j
      set M := data.reps (e.symm j) with hMdef
      have hMmax : M ∈ maximalSubgroups G := data.maximal (e.symm j)
      have hMI : IsTypeI M := hall _ hMmax
      -- `M_F ≠ ⊥` for the type-I maximal.
      have hMFne : maxNilpotentNormalHall M ≠ ⊥ := by
        obtain ⟨td⟩ := hMI
        rw [← td.typeF.H_eq]
        exact td.typeF.H_nontrivial
      -- `N_G(M_F) = M`.
      have hNorm : M = Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
        maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG hMmax hMFne
      -- `M_F#` is TI with normalizer `N_G(M_F)`, from `FittingIsTI M`; rewrite `N_G(M_F) = M` in
      -- the TI witness (not in the goal — that would fold `M` inside `maxNilpotentNormalHall M`).
      have hTI :=
        OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hMmax
          (allTypeI_fittingIsTI hG hMmax hMI hall)
      rw [← hNorm] at hTI
      -- `sharpSubgroup (maxNilpotentNormalHall M)` unfolds to `(maxNilpotentNormalHall M) \ {1}`.
      exact hTI
    · -- **`coprime`** (discharged): the kernels have pairwise-coprime order because the (8.17)
      -- partition makes their prime-factor sets disjoint.
      intro j j' hjj'
      have hne : e.symm j ≠ e.symm j' := fun h => hjj' (e.symm.injective h)
      have hdisj := data.primeFactors_disjoint (e.symm j) (e.symm j') hne
      simp only [hMF] at hdisj
      have hcard1 : Nat.card ↥(maxNilpotentNormalHall (data.reps (e.symm j))) ≠ 0 :=
        Nat.card_pos.ne'
      have hcard2 : Nat.card ↥(maxNilpotentNormalHall (data.reps (e.symm j'))) ≠ 0 :=
        Nat.card_pos.ne'
      exact (Nat.disjoint_primeFactors hcard1 hcard2).mp hdisj
    · -- **`covers`** (discharged): the faithful BG cover `𝒞_G(M̃_i)` lands in the conjugates of the
      -- kernel sharp-set `((M_i)_F)#` (`BGTheoremETypeICovering.cover_subset_kernels`; in the
      -- all-type-I case `R(x) = 1`, so `M̃_i = (M_i)_σ# = (M_i)_F#`).  Combined with the (8.17.a)
      -- cover `cover_nonidentity`, every nonidentity `x` is conjugate into some `(M_i)_F#`.
      intro x hx1
      have hxsharp : x ∈ sharpSubgroup (⊤ : Subgroup G) := by
        simp only [sharpSubgroup, Subgroup.coe_top, Set.mem_sdiff, Set.mem_univ, true_and,
          Set.mem_singleton_iff]
        exact hx1
      rw [hTypeI.cover_nonidentity] at hxsharp
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxsharp
      obtain ⟨t, htMF, g, hgtx⟩ := hTypeI.cover_subset_kernels i hxi
      refine ⟨e i, g⁻¹, ?_⟩
      have hreps : data.reps (e.symm (e i)) = data.reps i := by rw [Equiv.symm_apply_apply]
      have hconj : g⁻¹ * x * (g⁻¹)⁻¹ = t := by rw [inv_inv, ← hgtx]; group
      rw [hreps, hconj]
      exact htMF
  · -- **(8.8.b) non-type-I cover branch**: ruled out when every maximal subgroup is type I.
    -- This is the all-type-I case of the (8.8) dichotomy (`theorem88_dichotomy`); under `hall`
    -- BG Theorem E returns the type-I cover, never the two-exceptional-subgroup case (the
    -- exceptional `W` of `hNonTypeI` is the normalizer of a non-type-I maximal).  Isolating that
    -- is the BG §16 (8.8.a) residual (`not_nonTypeICovering_of_all_typeI`).
    exfalso
    obtain ⟨hcov⟩ := hNonTypeI
    exact not_nonTypeICovering_of_all_typeI hG hcov hall

/-- **Peterfalvi (12.17), non-existence half**: in a minimal simple group of odd order, not every
maximal subgroup is of type I.

*Proof.*  Assume otherwise.  The §8 covering theory (`exists_typeICovering`) provides the family of
conjugacy-class representatives `reps i` of the maximal subgroups, whose kernels `(reps i)_F` are
pairwise-coprime TI-subsets covering `G#`.  Each `reps i` is a Frobenius group with kernel
`(reps i)_F` by (12.7) (`typeI_frobenius`) and equals its own `N_G((reps i)_F)`
(`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`), so these data assemble into a Frobenius
family in the sense of (7.10) (`S09.FrobeniusFamily`).  The covering makes `G₀ = {1}`, contradicting
(7.11) (`S09.not_trivial_G0`). -/
theorem not_all_maximal_typeI (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ¬ (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) := by
  intro hall
  obtain ⟨cov⟩ := exists_typeICovering hG hall
  let F : OddOrder.Peterfalvi.S09.FrobeniusFamily G cov.k :=
    { L := cov.reps
      H := fun i => maxNilpotentNormalHall (cov.reps i)
      two_le := cov.two_le
      kernel_le := fun i => OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le (cov.reps i)
      isFrobenius := fun i => by
        obtain ⟨fd, -⟩ := typeI_frobenius hG (cov.reps_maximal i) (hall _ (cov.reps_maximal i))
        refine ⟨fd.complement, ?_⟩
        rw [← fd.typeI.typeF.H_eq]
        exact fd.frobenius
      normalizer_eq := fun i =>
        maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG (cov.reps_maximal i) (by
          obtain ⟨td⟩ := hall _ (cov.reps_maximal i)
          rw [← td.typeF.H_eq]
          exact td.typeF.H_nontrivial)
      isTI := cov.isTI
      coprime_kernel := cov.coprime }
  have hG0 : F.G0 = {(1 : G)} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨F.one_mem_G0, fun x hx => ?_⟩
    by_contra hx1
    obtain ⟨i, g, hg⟩ := cov.covers x hx1
    exact (F.mem_G0_iff.mp hx) i ⟨g, hg⟩
  exact OddOrder.Peterfalvi.S09.not_trivial_G0 F hG.odd hG0

end Theorem1217

/-! ## (12.17) → (8.8): the case-(b) dichotomy -/

/-- **Type-`P` ⟹ non-Type-I** (Proposition 16.1(b)(c)(d)): a type-`P` maximal subgroup of a minimal
simple group of odd order is one of the Types II–V.  Split `κ(M)` against `π(M) - σ(M)`: equal gives
`P₁`, which is Type V (`M_F = M_σ`) or Type III/IV (`M_F ≠ M_σ`); unequal gives `P₂` = Type II.  This
is the local `typeP_imp_nonI` of BG Theorem I's dichotomy proof, isolated here for
`theorem88_dichotomy`. -/
private theorem isTypeNonI_of_isTypeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N : Subgroup G} (hN : N ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP N) : IsTypeNonI N := by
  obtain ⟨_, hbII, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hN
  by_cases hk : OddOrder.BG.Ch4.S14.kappa N = OddOrder.BG.Ch4.S14.sigmaComplementPrimes N
  · have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 N := ⟨hP, hk⟩
    by_cases hMF : OddOrder.BG.Ch4.S15.MF N = OddOrder.BG.Ch3.S10.Msigma N
    · exact Or.inr (Or.inr (Or.inr (hdV.mpr ⟨hP1, hMF⟩)))
    · rcases hcIII_IV.mpr ⟨hP1, hMF⟩ with hIII | hIV
      · exact Or.inr (Or.inl hIII)
      · exact Or.inr (Or.inr (Or.inl hIV))
  · exact Or.inl (hbII.mpr ⟨hP, hk⟩)

/-- **Theorem (8.8) dichotomy** (BG §16): for a minimal simple group of odd order, either every
maximal subgroup is of type I, or the case-(b) pairing data `Theorem88CaseBData` exists.

*Proof.*  If some maximal `S` is not type I, then it is type `P` (Proposition 16.1(a): `TypeI ⟺
TypeF`, and `TypeF ⟺ κ(S) = ∅`).  BG Theorem 14.7 duality (`typeP_duality`) applied to `S` with a
`κ(S)`-Hall subgroup `K` produces the complement `S = S' ⋊ K` (first conjunct), the dual maximal
`T = M*`, the cyclic factor `W = K ⊔ K*`, the type-II witness, and the `κ(M*)`-Hall `K*`.  Applying
the duality again at `M*` gives the second complement `T = T' ⋊ K*`.  The `κ`-Hall complement `K`
plays the role of the case-(b) factor `W₁` (both `K` and the type-`P` `W₁` complement `S'`, Peterfalvi
(8.8.b1)).  Cites the merged BG §16 `typeP_duality` and `proposition_type_classification`; the
remaining hard content lives in their (issue-8015) residuals. -/
theorem theorem88_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) ∨
      Nonempty (OddOrder.Peterfalvi.S12.Theorem88CaseBData G) := by
  classical
  by_cases hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M
  · exact Or.inl hall
  · refine Or.inr ?_
    push Not at hall
    obtain ⟨S, hS, hSnotI⟩ := hall
    haveI : IsSolvable ↥S := hG.solvable_of_mem_maximalSubgroups hS
    -- `S` not type I ⟹ `S` type `P` (Prop 16.1(a): `TypeI ⟺ TypeF`, `TypeF ⟺ κ(S) = ∅`).
    have hSP : OddOrder.BG.Ch4.S14.IsTypeP S := by
      have hiff := (OddOrder.BG.Ch4.S16.proposition_type_classification hG hS).1
      have hnotF : ¬ OddOrder.BG.Ch4.S14.IsTypeF S := fun hF => hSnotI (hiff.mpr hF)
      rw [OddOrder.BG.Ch4.S14.IsTypeP, Set.nonempty_iff_ne_empty]
      exact fun he => hnotF he
    -- A `κ(S)`-Hall subgroup `K` of `S` (Hall's theorem in the solvable `S`).
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥S) (OddOrder.BG.Ch4.S14.kappa S)
    set K : Subgroup G := K'.map S.subtype with hKdef
    have hKeq : K.subgroupOf S = K' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S) (K.subgroupOf S) := by
      rw [hKeq]; exact hK'
    set Kstar : Subgroup G :=
      OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) with hKstardef
    -- BG Theorem 14.7 duality at `S`: `S = S' ⋊ K` (`hScompl`), the dual `M*`, its data.
    obtain ⟨hScompl, _, Mstar, ⟨hMstarMem, hMstarP, hSnconjMstar,
        ⟨hKstarMstar, hKstar_hall, hK_eq⟩, hcyc, _, hP2disj, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hS hSP (Subgroup.map_subtype_le K') hK hKstardef
    -- Apply duality again at `M*` with its `κ`-Hall `K*`: `M* = (M*)' ⋊ K*` (`hTcompl`).
    obtain ⟨hTcompl, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hMstarMem hMstarP hKstarMstar hKstar_hall hK_eq
    exact ⟨{
      S := S, T := Mstar, W1 := K, W2 := Kstar, W := K ⊔ Kstar
      S_maximal := hS, T_maximal := hMstarMem
      S_ne_T := by
        intro hST
        rw [hST] at hSnconjMstar
        exact hSnconjMstar (OddOrder.BG.Ch4.S14.IsConjugateSubgroup.refl Mstar)
      W_eq := rfl, W_cyclic := hcyc
      S_nonI := isTypeNonI_of_isTypeP hG hS hSP
      T_nonI := isTypeNonI_of_isTypeP hG hMstarMem hMstarP
      one_typeII := hP2disj.imp
        (fun h => (OddOrder.BG.Ch4.S16.proposition_type_classification hG hS).2.1.mpr h)
        (fun h => (OddOrder.BG.Ch4.S16.proposition_type_classification hG hMstarMem).2.1.mpr h)
      W1_le_S := Subgroup.map_subtype_le K'
      W2_le_T := hKstarMstar
      S_compl := hScompl
      T_compl := hTcompl }⟩

/-- **Peterfalvi (12.17)**: the all-type-I case of Theorem (8.8) is impossible, so the case-(b)
data of (8.8) exists.  Immediate from the (8.8) dichotomy (`theorem88_dichotomy`) and the
non-existence half `not_all_maximal_typeI`. -/
theorem theorem88_caseB_holds [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    Nonempty (OddOrder.Peterfalvi.S12.Theorem88CaseBData G) :=
  (theorem88_dichotomy hG).resolve_left (not_all_maximal_typeI hG)

end OddOrder.Peterfalvi.S14

#print axioms OddOrder.Peterfalvi.S14.frobenius_typeI_induced_char_constituents
#print axioms OddOrder.Peterfalvi.S14.fixed_conjClass_eq_one_of_typeF
#print axioms OddOrder.Peterfalvi.S14.coherent_extension_mem_span_imageFamily
#print axioms OddOrder.Peterfalvi.S14.coherent_extension_constituent_mem_span_Rset
#print axioms OddOrder.Peterfalvi.S14.constituent_diffImage_inner_zero_of_disjoint
-- `coherent_extension_constituent_orthogonal_Rset_of_nonconjugate` is sorry-free in its own body
-- but transitively cites `nonconjugate_typeI_R_orthogonal` (12.3).  The (12.3) bar-trick descent
-- (`constituent_diffImage_inner_zero_of_disjoint`, axiom-clean, 2026-07-03) closed the geometric
-- obligation `nonconjugate_diffImage_inner_zero`; its residual transitive `sorryAx` comes from the
-- §10 (8.18.c)/(8.15) support pins (§16-gated) and the (12.2.a) constituent obligation
-- `typeI_induced_char_constituents` ((8.2.c)); so it stays *out* of the axiom-clean block above.

