import OddOrder.Peterfalvi.S15_CaseASylowCenter

/-!
# Peterfalvi (14.6) — the order of `Ω₁(Z(R))` in case A

In case (9.7.a), (13.12) gives `c = 1`.  Thus the kernel of the action of the actual
subgroup `U` on the chief factor is trivial, and the two-block scalar map embeds `U` in
two cyclic scalar coordinates.  Consequently `rank U ≤ 2`.

For the ambient Sylow subgroup constructed in `S15_CaseASylowCenter`, the subgroup
`Ω₁(Z(R))` is nontrivial, elementary abelian, and lies in `R₀ ≤ U`.  The rank bound then
forces its order to be `r` or `r²`, as in Peterfalvi (14.6).

Peterfalvi, *Character Theory for the Odd Order Theorem*, (14.6).
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-! ## Two cyclic coordinates have rank at most two -/

/-- An elementary abelian subgroup of a product of two cyclic groups has logarithmic
prime order at most two.  Projecting to the first coordinate gives a cyclic image; its
kernel embeds in the second coordinate and is cyclic as well. -/
private theorem rank_pi_fin_two_le_two_of_isCyclic
    {C : Type*} [Group C] [Finite C] [IsCyclic C] :
    rank (Fin 2 → C) ≤ 2 := by
  rw [rank_le_iff]
  intro r hr
  rw [pRank_le_iff]
  intro A hA
  let π0 : ↥A →* C :=
    (Pi.evalMonoidHom (fun _ : Fin 2 => C) 0).comp A.subtype
  let π1 : ↥π0.ker →* C :=
    (Pi.evalMonoidHom (fun _ : Fin 2 => C) 1).comp
      (A.subtype.comp π0.ker.subtype)
  have hπ1 : Function.Injective π1 := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
    · have hx0 : π0 (x : ↥A) = 1 := x.2
      have hy0 : π0 (y : ↥A) = 1 := y.2
      simpa only [π0, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
        Subgroup.coe_subtype] using hx0.trans hy0.symm
    · simpa only [π1, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
        Subgroup.coe_subtype, Fin.succ_zero_eq_one] using hxy
  letI : IsCyclic ↥π0.ker := isCyclic_of_injective π1 hπ1
  have hker_dvd : Nat.card ↥π0.ker ∣ r := by
    rw [← IsCyclic.exponent_eq_card (α := ↥π0.ker)]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    exact hA.pow_eq_one (x : ↥A)
  have hker_le : Nat.card ↥π0.ker ≤ r := Nat.le_of_dvd hr.pos hker_dvd
  letI : IsCyclic ↥π0.range := Subgroup.isCyclic π0.range
  have hrange_dvd : Nat.card ↥π0.range ∣ r := by
    rw [← IsCyclic.exponent_eq_card (α := ↥π0.range)]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    obtain ⟨a, ha⟩ := x.2
    apply Subtype.ext
    change (x : C) ^ r = 1
    rw [← ha, ← map_pow, hA.pow_eq_one, map_one]
  have hrange_le : Nat.card ↥π0.range ≤ r := Nat.le_of_dvd hr.pos hrange_dvd
  have hcard : Nat.card ↥π0.ker * Nat.card ↥π0.range = Nat.card ↥A := by
    rw [← Subgroup.index_ker π0]
    exact Subgroup.card_mul_index π0.ker
  have hcard_le : Nat.card ↥A ≤ r ^ 2 := by
    rw [← hcard, pow_two]
    exact Nat.mul_le_mul hker_le hrange_le
  calc
    Nat.log r (Nat.card ↥A) ≤ Nat.log r (r ^ 2) := Nat.log_mono_right hcard_le
    _ = 2 := Nat.log_pow hr.one_lt 2

/-! ## The actual case-A subgroup `U` has rank at most two -/

/-- **Peterfalvi (14.6), two-coordinate rank bound.**  In case (9.7.a), after
`c = 1` and `q = 3`, the actual subgroup `U` embeds in two copies of `(ZMod p)ˣ`
and hence has BG rank at most two.

The qualitative §9 embedding is initially stated for the faithful action image.  Here
The two numerical conclusions are explicit inputs: their current unconditional producers
run through the (13.10) relayer tracked by issue 0116.  Together with `cSub = C`, `c = 1`
makes the original action faithful and therefore lifts the embedding to `U` itself. -/
theorem caseA_rank_U_le_two_of_c_eq_one_q_eq_three [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hc : hyp.c = 1)
    (hq : hyp.q = 3) :
    rank ↥hyp.U ≤ 2 := by
  classical
  let data := hyp.toTypesIIIIIIVSetupS hG
  let action := OddOrder.Peterfalvi.S11.uActionHom data chief
  haveI : Fact chief.p.Prime := ⟨chief.p_prime⟩
  obtain ⟨ψ, hψ⟩ :=
    OddOrder.Peterfalvi.S11.caseA_exists_blockScalarRatioEmbedding
      (hyp.mkSection11CharacterDataS hG chief) caseA
  have hqsub : data.q - 1 = 2 := by
    rw [show data.q = hyp.q from hyp.toTypesIIIIIIVSetupS_q_eq hG, hq]
  let eFin : Fin (data.q - 1) ≃ Fin 2 := finCongr hqsub
  let ψ2 : ↥(MonoidHom.range action) →* (Fin 2 → (ZMod chief.p)ˣ) :=
    { toFun := fun u i => ψ u (eFin.symm i)
      map_one' := by ext i; simp
      map_mul' := fun x y => by ext i; simp }
  have hψ2 : Function.Injective ψ2 := by
    intro x y hxy
    apply hψ
    funext j
    have hij := congrFun hxy (eFin j)
    simpa only [ψ2, MonoidHom.coe_mk, OneHom.coe_mk,
      Equiv.symm_apply_apply] using hij
  have hker_card : Nat.card ↥action.ker = 1 := by
    rw [← OddOrder.Peterfalvi.S11.card_cSub_eq_card_ker data chief,
      hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief,
      ← hyp.c_eq_card_C, hc]
  have haction : Function.Injective action :=
    action.ker_eq_bot_iff.mp (Subgroup.card_eq_one.mp hker_card)
  let eU : ↥hyp.U ≃* ↥data.U := MulEquiv.subgroupCongr hyp.Sdata_U_eq.symm
  let eAction : ↥data.U ≃*
      ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
  let φ : ↥hyp.U →* ↥(MonoidHom.range action) :=
    action.rangeRestrict.comp (eAction.toMonoidHom.comp eU.toMonoidHom)
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply eU.injective
    apply eAction.injective
    apply haction
    exact congrArg Subtype.val hxy
  let ψU : ↥hyp.U →* (Fin 2 → (ZMod chief.p)ˣ) := ψ2.comp φ
  have hψU : Function.Injective ψU := hψ2.comp hφ
  exact (rank_le_of_injective hψU).trans rank_pi_fin_two_le_two_of_isCyclic

/-! ## `Ω₁(Z(R))` has order `r` or `r²` -/

/-- **Peterfalvi (14.6), order of the Sylow center layer.**  Let `R₀ ∈ Syl_r(U)` be
noncyclic, let `R ∈ Syl_r(K)` contain its image, and suppose the ambient center of `R`
has been trapped in `R₀`.  If `rank U ≤ 2`, then the ambient subgroup
`Ω₁(Z(R))` has order `r` or `r²`.

Nontriviality is the standard fact that the center of a nontrivial finite `r`-group
contains an element of order `r`.  The order alternatives then follow from the generic
elementary-abelian rank squeeze. -/
theorem omega1Center_card_eq_prime_or_sq_of_rank_U_le_two [Finite G]
    {r : ℕ} (hr : r.Prime) (U K : Subgroup G) (hUK : U ≤ K)
    (hrankU : rank ↥U ≤ 2)
    (R₀ : Sylow r ↥U) (hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥U))
    (R : Sylow r ↥K)
    (hR₀R : (R₀ : Subgroup ↥U).map (Subgroup.inclusion hUK) ≤ R)
    (hcenter :
      (Subgroup.center ↥((R : Subgroup ↥K).map K.subtype)).map
          ((R : Subgroup ↥K).map K.subtype).subtype ≤
        (R₀ : Subgroup ↥U).map U.subtype) :
    Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥K).map K.subtype) r) = r ∨
      Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥K).map K.subtype) r) = r ^ 2 := by
  classical
  letI : Fact r.Prime := ⟨hr⟩
  let Rg : Subgroup G := (R : Subgroup ↥K).map K.subtype
  let R₀g : Subgroup G := (R₀ : Subgroup ↥U).map U.subtype
  let Z : Subgroup G := OddOrder.BG.Ch3.S10.omega1CenterInG Rg r
  have hR₀gRg : R₀g ≤ Rg := by
    rintro y ⟨u, hu, rfl⟩
    exact ⟨Subgroup.inclusion hUK u, hR₀R (Subgroup.mem_map_of_mem _ hu), rfl⟩
  have hR₀gU : R₀g ≤ U := Subgroup.map_subtype_le _
  have hrankR₀g : rank ↥R₀g ≤ 2 :=
    (rank_le_of_injective
      (f := Subgroup.inclusion hR₀gU) (Subgroup.inclusion_injective hR₀gU)).trans hrankU
  have hZelem : Z.IsElementaryAbelian r := by
    simpa only [Z, Rg, OddOrder.BG.Ch3.S10.omega1CenterInG,
      OddOrder.BG.Ch1.S05.omega1Center] using
      (Subgroup.IsElementaryAbelian.map Rg.subtype_injective
        (OddOrder.BG.Ch1.S05.omega1Center_isElementaryAbelian
          (R := ↥Rg) (p := r)))
  have hZcenter : Z ≤ (Subgroup.center ↥Rg).map Rg.subtype := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩
  have hZR₀g : Z ≤ R₀g := hZcenter.trans hcenter
  have hR₀_ne : (R₀ : Subgroup ↥U) ≠ ⊥ := by
    intro hbot
    apply hR₀nc
    rw [hbot]
    exact isCyclic_of_subsingleton
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR₀_ne
  have hRg_ne : Rg ≠ ⊥ := by
    intro hbot
    have haRg : (a : G) ∈ Rg :=
      hR₀gRg (Subgroup.mem_map_of_mem U.subtype a.2)
    have haG : (a : G) = 1 := Subgroup.mem_bot.mp (hbot ▸ haRg)
    exact ha1 (Subtype.ext (Subtype.ext haG))
  haveI : Nontrivial ↥Rg := (Subgroup.nontrivial_iff_ne_bot Rg).mpr hRg_ne
  have hRgpg : IsPGroup r Rg := by
    simpa only [Rg] using R.isPGroup'.map K.subtype
  obtain ⟨z, -, hzcenter, hz1, hzpow⟩ :=
    OddOrder.GroupTheory.exists_mem_omega1_center_of_normal_ne_bot
      (P := ↥Rg) (p := r) hRgpg (N := ⊤) (by exact top_ne_bot)
  have hzZ : (z : G) ∈ Z := by
    simpa only [Z, OddOrder.BG.Ch3.S10.omega1CenterInG,
      OddOrder.BG.Ch1.S05.omega1Center] using
      (show (z : G) ∈
          (OddOrder.BG.Ch1.S05.omega1Center (↥Rg) r).map Rg.subtype from
        ⟨z, ⟨hzcenter, hzpow⟩, rfl⟩)
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have hzbot : (z : G) ∈ (⊥ : Subgroup G) := hbot ▸ hzZ
    exact hz1 (Subtype.ext (Subgroup.mem_bot.mp hzbot))
  simpa only [Z, Rg] using
    (card_eq_prime_or_sq_of_isElementaryAbelian_le hZelem hZR₀g hrankR₀g hZne)

/-- **Peterfalvi (14.6), case-(9.7.a) specialization.**  Given the conclusions
`c = 1` of (13.12) and `q = 3` of (13.13), the preceding faithful two-coordinate
argument proves the rank hypothesis and determines the order of `Ω₁(Z(R))`. -/
theorem caseA_omega1Center_card_eq_prime_or_sq_of_parameters [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hc : hyp.c = 1) (hq : hyp.q = 3)
    {r : ℕ} (hr : r.Prime)
    (R₀ : Sylow r ↥hyp.U) (hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥hyp.U))
    (K : Subgroup G) (hUK : hyp.U ≤ K) (R : Sylow r ↥K)
    (hR₀R : (R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUK) ≤ R)
    (hcenter :
      (Subgroup.center ↥((R : Subgroup ↥K).map K.subtype)).map
          ((R : Subgroup ↥K).map K.subtype).subtype ≤
        (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype) :
    Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥K).map K.subtype) r) = r ∨
      Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥K).map K.subtype) r) = r ^ 2 := by
  exact omega1Center_card_eq_prime_or_sq_of_rank_U_le_two hr hyp.U K hUK
    (caseA_rank_U_le_two_of_c_eq_one_q_eq_three hG hyp caseA hc hq)
    R₀ hR₀nc R hR₀R hcenter

end OddOrder.Peterfalvi.S15
