import OddOrder.Peterfalvi.S15_SAndTDefs

/-!
# Peterfalvi (14.6) — trapping the case-A Sylow center

This leaf continues the case-(9.7.a) argument after the order determination of (13.13).
For `R₀ ∈ Syl_r(U)` and an ambient `R ∈ Syl_r(K)` containing it, the BG Proposition 1.16
witness lies in the honest type-`P₂` TI-set of `S`. Hence its centralizer lies in `S`;
Sylow maximality then identifies `C_R(x)` with `R₀`, and traps `Z(R)` in `R₀`.

Peterfalvi, *Character Theory for the Odd Order Theorem*, (14.6).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-! ## (14.6): the case-(9.7.a) Sylow center -/

/-- **Peterfalvi (14.6), Hall property of the `S`-side complement.** The named subgroup
`U` is a Hall subgroup of `S`, in cardinal form: `|U|` is coprime to `[S : U]`.

Indeed `[S : U] = |P| |W₁|`. The first factor is coprime to `|U|` because
`P` is complemented by `U ⋊ W₁` in `S`; the second is coprime to `|U|` because
`U ⋊ W₁` is a Frobenius group. -/
theorem coprime_card_U_index_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nat.Coprime (Nat.card ↥hyp.U) ((hyp.U.subgroupOf hyp.S).index) := by
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hUleS : hyp.U ≤ hyp.S :=
    (le_sup_right.trans hyp.S_deriv_eq_PU.ge).trans hM'_le_S
  have hPleM' : hyp.P ≤ derivedInG hyp.S := le_sup_left.trans hyp.S_deriv_eq_PU.ge
  have hcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P) :=
    (coprime_card_P_card_UW1 hG hyp).symm.coprime_dvd_left
      (Subgroup.card_dvd_of_le (le_sup_left : hyp.U ≤ hyp.U ⊔ hyp.W1))
  obtain ⟨bdata, -⟩ := basic_structure hG hyp
  have frobcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.W1) := by
    have h := bdata.UW1_frobenius.coprime_card_kernel_complement
    rwa [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : hyp.U ≤ hyp.U ⊔ hyp.W1)).toEquiv,
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (le_sup_right : hyp.W1 ≤ hyp.U ⊔ hyp.W1)).toEquiv] at h
  have hidxM' : ((derivedInG hyp.S).subgroupOf hyp.S).index = Nat.card ↥hyp.W1 := by
    rw [← hyp.Sdata_W1_eq, ← hyp.Sdata.card_W1_eq_derived_index]
  have hidxP : (hyp.P.subgroupOf (derivedInG hyp.S)).index = Nat.card ↥hyp.U := by
    rw [hyp.P_eq_SF, ← hyp.Sdata.card_U_eq_index, hyp.Sdata_U_eq]
  have hScard : Nat.card ↥hyp.S =
      Nat.card ↥hyp.W1 * (Nat.card ↥hyp.U * Nat.card ↥hyp.P) := by
    have e1 := ((derivedInG hyp.S).subgroupOf hyp.S).index_mul_card
    have e2 := (hyp.P.subgroupOf (derivedInG hyp.S)).index_mul_card
    rw [hidxM', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'_le_S).toEquiv] at e1
    rw [hidxP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleM').toEquiv] at e2
    rw [← e1, ← e2]
  have hidxU := (hyp.U.subgroupOf hyp.S).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleS).toEquiv] at hidxU
  have hidxUeq : (hyp.U.subgroupOf hyp.S).index =
      Nat.card ↥hyp.P * Nat.card ↥hyp.W1 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥hyp.U))
    rw [hidxU, hScard]
    ring
  rw [hidxUeq]
  exact hcop.mul_right frobcop

/-- **Peterfalvi (14.6), center trapping.** Let `R₀ ∈ Syl_r(U)` be noncyclic and let
`R ∈ Syl_r(K)` contain its image, where `U ≤ K`. If `x ∈ R₀#` is the BG Proposition 1.16
witness with `P ∩ C_G(x) ≠ 1`, then the center of the ambient image of `R` lies in the
ambient image of `R₀`.

The nontrivial point of `P ∩ C_G(x)` makes `x` a member of the honest type-`P₂` support
`A(S)`. Its TI property gives `C_G(x) ≤ S`. Since `U` is Hall in `S`, `R₀` is also
Sylow in `S`; the `r`-subgroup `R ∩ C_G(x)` contains `R₀` and lies in `S`, hence equals
`R₀`. -/
theorem sylow_center_le_U_sylow_of_centralizer_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {r : ℕ} (hr : r.Prime)
    (R₀ : Sylow r ↥hyp.U) (hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥hyp.U))
    (K : Subgroup G) (hUK : hyp.U ≤ K) (R : Sylow r ↥K)
    (hR₀R : (R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUK) ≤ R)
    {x : G} (hxR₀ : x ∈ (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype)
    (hx1 : x ≠ (1 : G))
    (hxP : hyp.P ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥) :
    (Subgroup.center ↥((R : Subgroup ↥K).map K.subtype)).map
        ((R : Subgroup ↥K).map K.subtype).subtype ≤
      (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype := by
  classical
  letI := Fintype.ofFinite G
  letI : Fact r.Prime := ⟨hr⟩
  have hUS : hyp.U ≤ hyp.S := by
    rw [← hyp.Sdata_U_eq]
    exact hyp.Sdata.U_le.trans (Subgroup.map_subtype_le _)
  have hR₀card : r ∣ Nat.card ↥(R₀ : Subgroup ↥hyp.U) :=
    R₀.isPGroup'.card_eq_or_dvd.resolve_left fun hcard => hR₀nc <| by
      letI : Subsingleton ↥(R₀ : Subgroup ↥hyp.U) :=
        (Nat.card_eq_one_iff_unique.mp hcard).1
      exact isCyclic_of_subsingleton
  have hrU : r ∣ Nat.card ↥hyp.U :=
    hR₀card.trans (Subgroup.card_subgroup_dvd_card (R₀ : Subgroup ↥hyp.U))
  have hrUindex : ¬ r ∣ (hyp.U.subgroupOf hyp.S).index :=
    hr.coprime_iff_not_dvd.mp
      ((coprime_card_U_index_S hG hyp).coprime_dvd_left hrU)
  let R₀S : Sylow r ↥hyp.S :=
    (R₀.isPGroup'.map (Subgroup.inclusion hUS)).toSylow <| by
      rw [(R₀ : Subgroup ↥hyp.U).index_map_of_injective
          (Subgroup.inclusion_injective hUS),
        Subgroup.inclusion_range]
      exact hr.not_dvd_mul R₀.not_dvd_index hrUindex
  let Rg : Subgroup G := (R : Subgroup ↥K).map K.subtype
  let Cx : Subgroup G := Rg ⊓ Subgroup.centralizer ({x} : Set G)
  have hxU : x ∈ hyp.U := Subgroup.map_subtype_le _ hxR₀
  have hR₀Rg : (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype ≤ Rg := by
    rintro y ⟨u, hu, rfl⟩
    exact ⟨Subgroup.inclusion hUK u, hR₀R (Subgroup.mem_map_of_mem _ hu), rfl⟩
  have hR₀Cx : (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype ≤ Cx := by
    refine le_inf hR₀Rg ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyU : y ∈ hyp.U := Subgroup.map_subtype_le _ hy
    exact congrArg Subtype.val <|
      hyp.S_U_commutative.is_comm.comm
        (⟨y, hyU⟩ : ↥hyp.U) (⟨x, hxU⟩ : ↥hyp.U)
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hxP
  obtain ⟨hzP, hzCx⟩ := Subgroup.mem_inf.mp z.2
  have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hPle_Ms : hyp.P ≤ OddOrder.BG.Ch3.S10.Msigma hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.S_maximal
  have hxA : x ∈ S10.typePACore hyp.S := by
    refine S10.mem_typePACore.mpr ⟨?_, hx1, (z : G), ⟨hPle_Ms hzP, ?_⟩, ?_⟩
    · have hUderived : hyp.U ≤ derivedInG hyp.S := by
        rw [hyp.S_deriv_eq_PU]
        exact le_sup_right
      exact hUderived hxU
    · rwa [Set.mem_singleton_iff]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hzCx).symm
  have hcentralizerS : Subgroup.centralizer ({x} : Set G) ≤ hyp.S :=
    (hyp.isTISubset_typePACore hG
      (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG)).centralizer_le hxA
  have hRgpg : IsPGroup r Rg := by
    simpa only [Rg] using R.isPGroup'.map K.subtype
  have hCxpg : IsPGroup r Cx := hRgpg.to_le inf_le_left
  have hCxS : Cx ≤ hyp.S := inf_le_right.trans hcentralizerS
  have hR₀S_le : (R₀S : Subgroup ↥hyp.S) ≤ Cx.subgroupOf hyp.S := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    change y ∈ (R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUS) at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact hR₀Cx (Subgroup.mem_map_of_mem hyp.U.subtype hu)
  have hCx_eq : Cx.subgroupOf hyp.S = (R₀S : Subgroup ↥hyp.S) :=
    R₀S.is_maximal' hCxpg.comap_subtype hR₀S_le
  rintro y ⟨yr, hyrZ, rfl⟩
  have hxRg : x ∈ Rg := hR₀Rg hxR₀
  have hyrC : (yr : G) ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hyrZ ⟨x, hxRg⟩)).symm
  have hyrCx : (yr : G) ∈ Cx := ⟨yr.2, hyrC⟩
  have hyrS : (yr : G) ∈ hyp.S := hCxS hyrCx
  let yS : ↥hyp.S := ⟨(yr : G), hyrS⟩
  have hySCx : yS ∈ Cx.subgroupOf hyp.S := hyrCx
  have hySR₀ : yS ∈ (R₀S : Subgroup ↥hyp.S) := by
    rw [← hCx_eq]
    exact hySCx
  change yS ∈ (R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUS) at hySR₀
  obtain ⟨u, hu, hueq⟩ := hySR₀
  exact ⟨u, hu, congrArg Subtype.val hueq⟩

/-- **Peterfalvi (14.6), ambient Sylow with trapped center.** The noncyclic `R₀` produces
an ambient Sylow `R`, a BG Proposition 1.16 witness `x`, and the conclusion `Z(R) ≤ R₀`
in one package. -/
theorem exists_sylow_over_U_with_trapped_center_of_not_isCyclic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (hyp.p - 1) / 2)
    (R₀ : Sylow r ↥hyp.U) (hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥hyp.U))
    (K : Subgroup G) (hUK : hyp.U ≤ K) :
    ∃ R : Sylow r ↥K,
      (R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUK) ≤ R ∧
        ∃ x ∈ (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype, x ≠ (1 : G) ∧
          hyp.P ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ ∧
            (Subgroup.center ↥((R : Subgroup ↥K).map K.subtype)).map
                ((R : Subgroup ↥K).map K.subtype).subtype ≤
              (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype := by
  obtain ⟨R, hR₀R, x, hxR₀, hx1, hxP⟩ :=
    exists_sylow_over_U_with_centralizer_witness_of_not_isCyclic
      hG hyp hr hrhalf R₀ hR₀nc K hUK
  exact ⟨R, hR₀R, x, hxR₀, hx1, hxP,
    sylow_center_le_U_sylow_of_centralizer_witness
      hG hyp hr R₀ hR₀nc K hUK R hR₀R hxR₀ hx1 hxP⟩

end OddOrder.Peterfalvi.S15
