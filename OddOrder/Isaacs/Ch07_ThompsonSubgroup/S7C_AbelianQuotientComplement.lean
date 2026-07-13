/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7C_CentralizerCenter

/-!
# Isaacs FGT Ch.7 — Theorem 7.1 Step 6: the quotient complement is abelian (p. 219)

This leaf proves the last structural input needed by the normal-J theorem.  In a
minimal counterexample, the normal `p`-complement of `G/O_p(G)` is abelian;
consequently every `2`-subgroup of `G` is abelian when `p ≠ 2`.
-/

namespace OddOrder.Isaacs.Ch07

open scoped IsMulCommutative

section MinimalCounterexampleStepSix

/-- **Isaacs Theorem 7.1, Step 6 (abelian quotient complement).**

Assume that the Sylow `p`-subgroup `P` is maximal.  If `Nbar` is a normal
`p`-complement in `G/O_p(G)`, then `Nbar` is abelian.  Indeed, the inverse image
of `Pbar ⊔ W` for a `Pbar`-invariant subgroup `W ≤ Nbar` contains `P`; maximality
forces it to be either `P` or all of `G`.  Dedekind's law then gives
`W = ⊥` or `W = Nbar`.  An invariant Sylow subgroup shows that `Nbar` is a
prime-power group, and its invariant proper derived subgroup must be trivial. -/
theorem quotientComplement_isMulCommutative_of_sylow_isCoatom.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP_max : IsCoatom (P : Subgroup G))
    {Nbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)}
    (hNbar_normal : Nbar.Normal)
    (hNbar_complement : ∀ Pbar : Sylow p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G),
      Subgroup.IsComplement' Nbar (Pbar : Subgroup
        (G ⧸ OddOrder.Isaacs.Ch01.opCore p G))) :
    IsMulCommutative ↥Nbar := by
  classical
  letI : Nbar.Normal := hNbar_normal
  let q : G →* G ⧸ OddOrder.Isaacs.Ch01.opCore p G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch01.opCore p G)
  have hq : Function.Surjective q :=
    QuotientGroup.mk'_surjective (OddOrder.Isaacs.Ch01.opCore p G)
  have hker : q.ker = OddOrder.Isaacs.Ch01.opCore p G := by
    dsimp [q]
    exact QuotientGroup.ker_mk' _
  set Pbar : Sylow p (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) :=
    P.mapSurjective hq with hPbar_def
  have hPbar_coe :
      (Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) =
        (P : Subgroup G).map q := by
    rw [hPbar_def, Sylow.coe_mapSurjective]
  have hPbar_comap :
      (Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)).comap q =
        (P : Subgroup G) := by
    rw [hPbar_coe]
    exact Subgroup.comap_map_eq_self
      (by simpa only [hker] using OddOrder.Isaacs.Ch01.opCore_le P)
  have hcomp := hNbar_complement Pbar
  let phi : ↥(Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) →*
      MulAut ↥Nbar :=
    (MulAut.conjNormal (H := Nbar)).comp
      (Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)).subtype
  have hphi_val : ∀
      (a : ↥(Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)))
      (n : ↥Nbar),
      (((phi a) n : ↥Nbar) : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) =
        (a : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) *
          (n : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) *
            (a : G ⧸ OddOrder.Isaacs.Ch01.opCore p G)⁻¹ := by
    intro a n
    simp only [phi, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulAut.conjNormal_apply]
  have hphi_inv_val : ∀
      (a : ↥(Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)))
      (n : ↥Nbar),
      (((phi a)⁻¹ n : ↥Nbar) : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) =
        (a : G ⧸ OddOrder.Isaacs.Ch01.opCore p G)⁻¹ *
          (n : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) *
            (a : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) := by
    intro a n
    simp only [phi, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact MulAut.conjNormal_inv_apply (a :
      G ⧸ OddOrder.Isaacs.Ch01.opCore p G) n
  have invariant_dichotomy
      (W : Subgroup ↥Nbar)
      (hW_inv : OddOrder.Isaacs.Ch03.IsAInvariant phi W) :
      W = ⊥ ∨ W = ⊤ := by
    set Wbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) :=
      W.map Nbar.subtype with hWbar_def
    have hWbar_le : Wbar ≤ Nbar := by
      rw [hWbar_def]
      exact Subgroup.map_subtype_le W
    have hPbar_normalizes_Wbar :
        (Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) ≤
          Subgroup.normalizer (Wbar : Set
            (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · rintro ⟨n, hn, rfl⟩
        refine ⟨(phi ⟨a, ha⟩) n, hW_inv.smul_mem ⟨a, ha⟩ hn, ?_⟩
        exact hphi_val ⟨a, ha⟩ n
      · rintro ⟨n, hn, hn_eq⟩
        refine ⟨(phi ⟨a, ha⟩)⁻¹ n,
          hW_inv.inv_smul_mem ⟨a, ha⟩ hn, ?_⟩
        simp only [Subgroup.coe_subtype] at hn_eq ⊢
        rw [hphi_inv_val ⟨a, ha⟩ n, hn_eq]
        group
    set Hbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) :=
      (Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) ⊔ Wbar
      with hHbar_def
    set H : Subgroup G := Hbar.comap q with hH_def
    have hP_le_H : (P : Subgroup G) ≤ H := by
      rw [hH_def, ← hPbar_comap]
      exact Subgroup.comap_mono (hHbar_def ▸ le_sup_left)
    have hH_map : H.map q = Hbar := by
      rw [hH_def]
      exact Subgroup.map_comap_eq_self_of_surjective hq Hbar
    rcases (hP_max.le_iff.mp hP_le_H) with hH_top | hH_P
    · have hHbar_top : Hbar = ⊤ := by
        calc
          Hbar = H.map q := hH_map.symm
          _ = (⊤ : Subgroup G).map q := by rw [hH_top]
          _ = ⊤ := Subgroup.map_top_of_surjective q hq
      have hmeet :
          (Wbar ⊔ (Pbar : Subgroup
            (G ⧸ OddOrder.Isaacs.Ch01.opCore p G))) ⊓ Nbar = Wbar :=
        Subgroup.inf_sup_eq_of_le_normalizer_of_inf_eq_bot
          hWbar_le hcomp.disjoint.symm.eq_bot hPbar_normalizes_Wbar
      have hWbar_eq : Wbar = Nbar := by
        calc
          Wbar =
              (Wbar ⊔ (Pbar : Subgroup
                (G ⧸ OddOrder.Isaacs.Ch01.opCore p G))) ⊓ Nbar :=
            hmeet.symm
          _ = Hbar ⊓ Nbar := by rw [hHbar_def, sup_comm]
          _ = Nbar := by rw [hHbar_top, top_inf_eq]
      right
      apply Subgroup.map_injective Nbar.subtype_injective
      rw [← hWbar_def, hWbar_eq, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    · have hHbar_Pbar :
          Hbar = (Pbar : Subgroup
            (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) := by
        calc
          Hbar = H.map q := hH_map.symm
          _ = (P : Subgroup G).map q := by rw [hH_P]
          _ = (Pbar : Subgroup
            (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) := hPbar_coe.symm
      have hWbar_le_Pbar :
          Wbar ≤ (Pbar : Subgroup
            (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) := by
        rw [← hHbar_Pbar, hHbar_def]
        exact le_sup_right
      have hWbar_bot : Wbar = ⊥ := by
        rw [← le_bot_iff, ← hcomp.disjoint.symm.eq_bot]
        exact le_inf hWbar_le_Pbar hWbar_le
      left
      rw [hWbar_def] at hWbar_bot
      exact (Subgroup.map_eq_bot_iff_of_injective _
        Nbar.subtype_injective).mp hWbar_bot
  by_cases hNbar_bot : Nbar = ⊥
  · haveI : Subsingleton ↥Nbar := by
      rw [hNbar_bot]
      infer_instance
    infer_instance
  haveI : Nontrivial ↥Nbar :=
    Nbar.nontrivial_iff_ne_bot.mpr hNbar_bot
  obtain ⟨r, hr_prime, hr_dvd⟩ :=
    Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥Nbar)).ne'
  letI : Fact r.Prime := ⟨hr_prime⟩
  have hp_not_dvd_Nbar : ¬ p ∣ Nat.card ↥Nbar := by
    intro hp_dvd
    apply Pbar.not_dvd_index
    simpa only [hcomp.index_eq_card] using hp_dvd
  have hcop : Nat.Coprime
      (Nat.card ↥(Pbar : Subgroup
        (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)))
      (Nat.card ↥Nbar) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Pbar.isPGroup'
    rw [hk]
    exact Nat.Coprime.pow_left k
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_Nbar)
  haveI : Group.IsNilpotent
      ↥(Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :=
    IsPGroup.isNilpotent Pbar.isPGroup'
  haveI : IsSolvable
      ↥(Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :=
    inferInstance
  obtain ⟨R, hR_inv⟩ :=
    OddOrder.Isaacs.Ch04.exists_aInvariant_sylow
      (A := ↥(Pbar : Subgroup
        (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)))
      (G := ↥Nbar) (φ := phi) hcop (Or.inl inferInstance) r
  have hR_ne : (R : Subgroup ↥Nbar) ≠ ⊥ :=
    R.ne_bot_of_dvd_card hr_dvd
  have hR_top : (R : Subgroup ↥Nbar) = ⊤ := by
    rcases invariant_dichotomy (R : Subgroup ↥Nbar) hR_inv with hR_bot | hR_top
    · exact (hR_ne hR_bot).elim
    · exact hR_top
  have hNbar_r : IsPGroup r ↥Nbar := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp R.isPGroup'
    apply IsPGroup.of_card (n := k)
    calc
      Nat.card ↥Nbar = Nat.card ↥(⊤ : Subgroup ↥Nbar) := by simp
      _ = Nat.card ↥(R : Subgroup ↥Nbar) := by rw [hR_top]
      _ = r ^ k := hk
  haveI : Group.IsNilpotent ↥Nbar := IsPGroup.isNilpotent hNbar_r
  haveI : IsSolvable ↥Nbar := inferInstance
  have hcomm_ne_top : commutator ↥Nbar ≠ ⊤ :=
    (IsSolvable.commutator_lt_top_of_nontrivial ↥Nbar).ne
  have hcomm_inv :
      OddOrder.Isaacs.Ch03.IsAInvariant phi (commutator ↥Nbar) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.commutator_self phi
  have hcomm_bot : commutator ↥Nbar = ⊥ := by
    rcases invariant_dichotomy (commutator ↥Nbar) hcomm_inv with hbot | htop
    · exact hbot
    · exact (hcomm_ne_top htop).elim
  exact (commutator_eq_bot_iff ↥Nbar).mp hcomm_bot

/-- **Isaacs Theorem 7.1, Step 6.**

In a minimal counterexample with `p ≠ 2`, every `2`-subgroup is abelian.  The
preceding theorem makes the normal `p`-complement `Nbar` of `G/O_p(G)` abelian.
The quotient map is injective on a `2`-subgroup because its kernel is a
`p`-group, and the image lies in `Nbar` because its order is coprime to the
index of that normal complement. -/
theorem twoSubgroups_commutative_of_minimal_counterexample.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp2 : p ≠ 2)
    (hHyp : HasThompsonPComplementHypothesis p G)
    (ih : ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H < Nat.card G →
      HasThompsonPComplementHypothesis p H →
      OddOrder.Isaacs.Ch05.HasNormalPComplement p H)
    (hG : ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (hQuotient : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :
    ∀ S : Subgroup G, IsPGroup 2 S →
      ∀ x y : ↥S, x * y = y * x := by
  classical
  obtain ⟨Nbar, hNbar_normal, hNbar_complement⟩ := hQuotient
  letI : Nbar.Normal := hNbar_normal
  have hP_max : IsCoatom (P : Subgroup G) :=
    sylow_isCoatom_of_minimal_counterexample P hHyp ih hG
      ⟨Nbar, hNbar_normal, hNbar_complement⟩
  have hNbar_comm : IsMulCommutative ↥Nbar :=
    quotientComplement_isMulCommutative_of_sylow_isCoatom
      P hP_max hNbar_normal hNbar_complement
  letI : IsMulCommutative ↥Nbar := hNbar_comm
  let q : G →* G ⧸ OddOrder.Isaacs.Ch01.opCore p G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch01.opCore p G)
  have hq : Function.Surjective q :=
    QuotientGroup.mk'_surjective (OddOrder.Isaacs.Ch01.opCore p G)
  have hker : q.ker = OddOrder.Isaacs.Ch01.opCore p G := by
    dsimp [q]
    exact QuotientGroup.ker_mk' _
  set Pbar : Sylow p (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) :=
    P.mapSurjective hq with hPbar_def
  have hcomp := hNbar_complement Pbar
  intro S hS_two x y
  have hU_p : IsPGroup p (OddOrder.Isaacs.Ch01.opCore p G) :=
    OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hS_U_coprime : Nat.Coprime (Nat.card ↥S)
      (Nat.card ↥(OddOrder.Isaacs.Ch01.opCore p G)) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS_two
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hU_p
    rw [ha, hb]
    exact ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr
      hp2.symm).pow a b
  have hS_inf_U : S ⊓ OddOrder.Isaacs.Ch01.opCore p G = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hS_U_coprime).eq_bot
  have hqS_injective : Function.Injective (q.comp S.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz_U : (z : G) ∈ OddOrder.Isaacs.Ch01.opCore p G := by
      have hz_ker : (z : G) ∈ q.ker := hz
      rw [hker] at hz_ker
      exact hz_ker
    have hz_inf : (z : G) ∈ S ⊓ OddOrder.Isaacs.Ch01.opCore p G :=
      ⟨z.2, hz_U⟩
    rw [hS_inf_U, Subgroup.mem_bot] at hz_inf
    exact Subtype.ext hz_inf
  set Sbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) :=
    S.map q with hSbar_def
  have hSbar_two : IsPGroup 2 Sbar := by
    rw [hSbar_def]
    exact hS_two.map q
  have hSbar_index_coprime : Nat.Coprime (Nat.card ↥Sbar) Nbar.index := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hSbar_two
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp Pbar.isPGroup'
    rw [hcomp.symm.index_eq_card, ha, hb]
    exact ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr
      hp2.symm).pow a b
  have hSbar_le_Nbar : Sbar ≤ Nbar :=
    Subgroup.le_of_coprime_card_index_of_normal hSbar_index_coprime
  have hx_Nbar : q (x : G) ∈ Nbar := by
    apply hSbar_le_Nbar
    rw [hSbar_def]
    exact ⟨x, x.2, rfl⟩
  have hy_Nbar : q (y : G) ∈ Nbar := by
    apply hSbar_le_Nbar
    rw [hSbar_def]
    exact ⟨y, y.2, rfl⟩
  apply hqS_injective
  have hcomm :
      (⟨q (x : G), hx_Nbar⟩ : ↥Nbar) *
          ⟨q (y : G), hy_Nbar⟩ =
        (⟨q (y : G), hy_Nbar⟩ : ↥Nbar) *
          ⟨q (x : G), hx_Nbar⟩ :=
    mul_comm _ _
  simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul,
    map_mul] using
    congrArg Subtype.val hcomm

end MinimalCounterexampleStepSix

end OddOrder.Isaacs.Ch07
