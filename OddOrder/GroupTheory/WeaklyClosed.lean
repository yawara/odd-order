/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Focal
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Weakly closed subgroups

I. M. Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 5C.6:

> Let `W ≤ H ≤ G`.  We say that `W` is **weakly closed** in `H` with respect to `G` if
> the only `G`-conjugate of `W` contained in `H` is `W` itself.

This file sets up the notion and proves the transport statement 5C.6(a): if `W` is
weakly closed in a Sylow subgroup `P`, then it is weakly closed in *every* Sylow
subgroup containing it.  (The statement is proved here for an arbitrary conjugate
`P^y` of `P`, which by Sylow's theorem covers all Sylow subgroups.)

Weak closure is the hypothesis of the Hall–Wielandt/Grün transfer theorems; see
issue 9503, where it is used for the Sylow `3`-subgroup of Peterfalvi Part II, Ch. II,
step (17).
-/

set_option autoImplicit false

open scoped commutatorElement

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **Weakly closed subgroup** (Isaacs, Problem 5C.6): the only `G`-conjugate of `W`
contained in `P` is `W` itself.  (The containment `W ≤ P` is not part of the
definition; it is carried separately where needed.) -/
def IsWeaklyClosed (W P : Subgroup G) : Prop :=
  ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ P →
    W.map (MulAut.conj g).toMonoidHom = W

/-- Conjugating twice is conjugating by the product. -/
theorem map_conj_map_conj (W : Subgroup G) (g h : G) :
    (W.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
      = W.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj, mul_assoc]

@[simp]
theorem map_conj_one (W : Subgroup G) :
    W.map (MulAut.conj (1 : G)).toMonoidHom = W := by
  ext x
  simp [MulAut.conj]

/-- Conjugation preserves containment. -/
theorem map_conj_le_map_conj {W P : Subgroup G} (g : G) (h : W ≤ P) :
    W.map (MulAut.conj g).toMonoidHom ≤ P.map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_mono h

/-- Conjugation reflects containment. -/
theorem le_of_map_conj_le_map_conj {W P : Subgroup G} {g : G}
    (h : W.map (MulAut.conj g).toMonoidHom ≤ P.map (MulAut.conj g).toMonoidHom) :
    W ≤ P := by
  have h' := map_conj_le_map_conj g⁻¹ h
  rwa [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel, map_conj_one,
    map_conj_one] at h'

/-- **Isaacs Problem 5C.6(a)**: weak closure transports to every conjugate containing
`W`.  If `W` is weakly closed in `P` and `W ≤ P^y`, then `W` is weakly closed in `P^y`.

Since any two Sylow `p`-subgroups are conjugate, this says that a subgroup weakly
closed in one Sylow subgroup is weakly closed in every Sylow subgroup containing it. -/
theorem IsWeaklyClosed.map_conj {W P : Subgroup G} (hwc : IsWeaklyClosed W P) {y : G}
    (hWQ : W ≤ P.map (MulAut.conj y).toMonoidHom) :
    IsWeaklyClosed W (P.map (MulAut.conj y).toMonoidHom) := by
  -- first, `W^{y⁻¹} = W`
  have hWy : W.map (MulAut.conj y⁻¹).toMonoidHom = W := by
    refine hwc y⁻¹ ?_
    have h := map_conj_le_map_conj y⁻¹ hWQ
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
  have hWy' : W.map (MulAut.conj y).toMonoidHom = W := by
    conv_lhs => rw [← hWy]
    rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]
  intro g hg
  -- `W^{y⁻¹g} ≤ P`, so it equals `W`
  have h1 : W.map (MulAut.conj (y⁻¹ * g)).toMonoidHom ≤ P := by
    have h := map_conj_le_map_conj y⁻¹ hg
    rw [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
    exact h
  have h2 := hwc _ h1
  -- conjugate back by `y`
  have h3 := congrArg (fun K : Subgroup G => K.map (MulAut.conj y).toMonoidHom) h2
  simp only [map_conj_map_conj] at h3
  rw [show y * (y⁻¹ * g) = g by group] at h3
  rw [h3, hWy']

section /- Conjugating two `p`-subgroups into a common Sylow subgroup -/

variable {p : ℕ} [Fact p.Prime]

/-- **Two `p`-subgroups of a subgroup `C` are conjugate (inside `C`) into a common
`p`-subgroup.**  Take Sylow `p`-subgroups `U ⊇ X` and `U' ⊇ Y` of `C` and conjugate `U'`
onto `U` by an element of `C`. -/
theorem exists_mem_conj_le_common [Finite G] {C X Y : Subgroup G}
    (hX : X ≤ C) (hY : Y ≤ C) (hXp : IsPGroup p ↥X) (hYp : IsPGroup p ↥Y) :
    ∃ c ∈ C, ∃ T : Subgroup G, IsPGroup p ↥T ∧ X ≤ T
      ∧ Y.map (MulAut.conj c).toMonoidHom ≤ T := by
  classical
  -- transport `X`, `Y` into `↥C`
  have hXC : IsPGroup p ↥(X.subgroupOf C) :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hX).symm
  have hYC : IsPGroup p ↥(Y.subgroupOf C) :=
    hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hY).symm
  obtain ⟨U, hU⟩ := hXC.exists_le_sylow
  obtain ⟨U', hU'⟩ := hYC.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥C) U' U
  refine ⟨(c : G), c.2, (U : Subgroup ↥C).map C.subtype, ?_, ?_, ?_⟩
  · exact U.2.of_equiv (Subgroup.equivMapOfInjective (U : Subgroup ↥C) C.subtype
      (Subgroup.subtype_injective C))
  · intro z hz
    exact ⟨⟨z, hX hz⟩, hU (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  · rintro - ⟨z, hz, rfl⟩
    refine ⟨c * ⟨z, hY hz⟩ * c⁻¹, ?_, rfl⟩
    have hzU' : (⟨z, hY hz⟩ : ↥C) ∈ (U' : Subgroup ↥C) :=
      hU' (Subgroup.mem_subgroupOf.mpr hz)
    have hmem : (c * ⟨z, hY hz⟩ * c⁻¹ : ↥C) ∈ ((c • U' : Sylow p ↥C) : Subgroup ↥C) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨⟨z, hY hz⟩, hzU', rfl⟩
    rwa [hc] at hmem

omit [Fact p.Prime] in
/-- A subgroup of a `p`-group is a `p`-group. -/
theorem isPGroup_of_le {W P : Subgroup G} (hP : IsPGroup p ↥P) (h : W ≤ P) :
    IsPGroup p ↥W :=
  (hP.to_subgroup (W.subgroupOf P)).of_equiv (Subgroup.subgroupOfEquivOfLe h)

/-- Membership in the normalizer, read off from invariance of the subgroup. -/
theorem mem_normalizer_of_map_conj_eq {W : Subgroup G} {n : G}
    (h : W.map (MulAut.conj n).toMonoidHom = W) : n ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [← h]
    exact ⟨w, hw, rfl⟩
  · intro hw
    rw [← h] at hw
    obtain ⟨v, hv, hvw⟩ := hw
    have hvw' : n * v * n⁻¹ = n * w * n⁻¹ := by
      simpa [MulAut.conj_apply] using hvw
    have hveq : v = w := mul_left_cancel (mul_right_cancel hvw')
    rwa [← hveq]

/-- **Isaacs Problem 5C.6(d)**: if `W ≤ Z(P)` is weakly closed in the Sylow
`p`-subgroup `P` with respect to `G`, then `N_G(W)` controls `G`-fusion in `P`:
two elements of `P` that are conjugate in `G` are already conjugate by an element of
`N_G(W)`.

**Proof** (Isaacs' hint): with `y = x^g`, both `W` and `W^g` centralise `y`, so they are
`p`-subgroups of `C = C_G(y)`; conjugating by some `c ∈ C` puts them in a common Sylow
`p`-subgroup of `C`, hence in a common Sylow `p`-subgroup `T` of `G`.  As `W` is weakly
closed in `T` (5C.6(a)), `W^{cg} = W`, i.e. `cg ∈ N_G(W)`, and `x^{cg} = y^c = y`. -/
theorem exists_mem_normalizer_conj_eq [Finite G] {W : Subgroup G} {P : Sylow p G}
    (hWP : W ≤ (P : Subgroup G))
    (hWZ : W ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hwc : IsWeaklyClosed W (P : Subgroup G))
    {x g : G} (hx : x ∈ (P : Subgroup G)) (hgx : g * x * g⁻¹ ∈ (P : Subgroup G)) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), g * x * g⁻¹ = n * x * n⁻¹ := by
  classical
  set y : G := g * x * g⁻¹ with hy_def
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hC_def
  -- `W` and `W^g` centralise `y`
  have hWC : W ≤ C := by
    intro w hw
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    exact (Subgroup.mem_centralizer_iff.mp (hWZ hw) y hgx).symm
  have hWgC : W.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro - ⟨w, hw, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hxw := Subgroup.mem_centralizer_iff.mp (hWZ hw) x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * w * g⁻¹ * y = g * (w * x) * g⁻¹ := by rw [hy_def]; group
      _ = g * (x * w) * g⁻¹ := by rw [hxw]
      _ = y * (g * w * g⁻¹) := by rw [hy_def]; group
  -- both are `p`-groups
  have hWp : IsPGroup p ↥W := isPGroup_of_le P.2 hWP
  have hWgp : IsPGroup p ↥(W.map (MulAut.conj g).toMonoidHom) :=
    hWp.of_equiv (Subgroup.equivMapOfInjective W (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)
  -- conjugate them into a common `p`-subgroup, then into a common Sylow subgroup
  obtain ⟨c, hcC, T, hTp, hWT, hWgT⟩ := exists_mem_conj_le_common hWC hWgC hWp hWgp
  obtain ⟨T', hTT'⟩ := hTp.exists_le_sylow
  -- `W` is weakly closed in `T'`
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq G P T'
  have hT'eq : (T' : Subgroup G) = (P : Subgroup G).map (MulAut.conj z).toMonoidHom := by
    rw [← hz, Sylow.coe_subgroup_smul]
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
  have hwcT : IsWeaklyClosed W (T' : Subgroup G) := by
    rw [hT'eq]
    exact hwc.map_conj (by rw [← hT'eq]; exact le_trans hWT hTT')
  -- hence `cg` normalises `W`
  have hconj : W.map (MulAut.conj (c * g)).toMonoidHom = W := by
    refine hwcT (c * g) ?_
    rw [← map_conj_map_conj]
    exact le_trans hWgT hTT'
  refine ⟨c * g, mem_normalizer_of_map_conj_eq hconj, ?_⟩
  have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  calc y = c * y * c⁻¹ := by rw [hcy]; group
    _ = c * g * x * g⁻¹ * c⁻¹ := by rw [hy_def]; group
    _ = (c * g) * x * (c * g)⁻¹ := by group

/-- If `p` does not divide the order of the abelianisation, a Sylow `p`-subgroup lies in
the derived subgroup. -/
theorem sylow_le_commutator_of_not_dvd [Finite G] (P : Sylow p G)
    (h : ¬ p ∣ Nat.card (Abelianization G)) : (P : Subgroup G) ≤ commutator G := by
  intro x hx
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.2) (⟨x, hx⟩ : ↥(P : Subgroup G))
  rw [Subgroup.orderOf_mk] at hk
  have hdvd1 : orderOf (Abelianization.of x) ∣ orderOf x := orderOf_map_dvd _ _
  have hdvd2 : orderOf (Abelianization.of x) ∣ Nat.card (Abelianization G) :=
    orderOf_dvd_natCard _
  rw [hk] at hdvd1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out (p := p.Prime))).mp hdvd1
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hj
  · exfalso
    refine h (dvd_trans ?_ hdvd2)
    rw [hj]
    exact dvd_pow_self p hjpos.ne'

/-- Conversely, if a Sylow `p`-subgroup lies in the derived subgroup then `p` does not
divide the order of the abelianisation. -/
theorem not_dvd_card_abelianization_of_sylow_le_commutator [Finite G] (P : Sylow p G)
    (h : (P : Subgroup G) ≤ commutator G) : ¬ p ∣ Nat.card (Abelianization G) := by
  intro hdvd
  rw [show Nat.card (Abelianization G) = (commutator G).index from
    (Subgroup.index_eq_card _).symm] at hdvd
  exact P.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le h))

omit [Fact p.Prime] in
/-- **Fusion control implies focal-subgroup control**: if every `G`-fusion between
elements of `P` is realised in `N`, the focal subgroup of `P` in `G` is already the
focal subgroup of `P` in `N`. -/
theorem focalSubgroup_le_map_of_fusion_control [Finite G] {N : Subgroup G} {P : Sylow p G}
    (hPN : (P : Subgroup G) ≤ N)
    (hcontrol : ∀ x g : G, x ∈ (P : Subgroup G) → g * x * g⁻¹ ∈ (P : Subgroup G) →
      ∃ n ∈ N, g * x * g⁻¹ = n * x * n⁻¹) :
    (P : Subgroup G).focalSubgroup
      ≤ ((((P : Subgroup G).subgroupOf N).focalSubgroup).map N.subtype) := by
  rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
  rintro z ⟨hzP, x, hx, u, rfl⟩
  -- `u * x * u⁻¹ ∈ P`, so the fusion is realised by some `n ∈ N`
  have hw : u * x⁻¹ * u⁻¹ ∈ (P : Subgroup G) := by
    have h1 : u * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by
      rw [commutatorElement_def]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hzP
  have hux : u * x * u⁻¹ ∈ (P : Subgroup G) := by
    have h2 : u * x * u⁻¹ = (u * x⁻¹ * u⁻¹)⁻¹ := by group
    rw [h2]
    exact Subgroup.inv_mem _ hw
  obtain ⟨n, hnN, hn⟩ := hcontrol x u hx hux
  have hzN : ⁅x, u⁆ ∈ N := hPN hzP
  refine ⟨⟨⁅x, u⁆, hzN⟩, ?_, rfl⟩
  -- as an element of `↥N` it is the commutator of `x` with `n`
  have hxN : x ∈ N := hPN hx
  have heq : (⟨⁅x, u⁆, hzN⟩ : ↥N) = ⁅(⟨x, hxN⟩ : ↥N), (⟨n, hnN⟩ : ↥N)⁆ := by
    refine Subtype.ext ?_
    change ⁅x, u⁆ = x * n * x⁻¹ * n⁻¹
    rw [commutatorElement_def]
    calc x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      _ = x * (u * x * u⁻¹)⁻¹ := by group
      _ = x * (n * x * n⁻¹)⁻¹ := by rw [hn]
      _ = x * n * x⁻¹ * n⁻¹ := by group
  rw [heq, Subgroup.focalSubgroup_def]
  refine Subgroup.subset_closure ⟨?_, ⟨x, hxN⟩, ?_, ⟨n, hnN⟩, rfl⟩
  · rw [Subgroup.mem_subgroupOf, ← heq]
    exact hzP
  · rw [Subgroup.mem_subgroupOf]
    exact hx

/-- **Weakly closed central subgroups control the `p`-transfer** (Isaacs Problem 5C.6(d)
together with the focal subgroup theorem): if `W ≤ Z(P)` is weakly closed in the Sylow
`p`-subgroup `P` with respect to `G`, then `p` divides `|G^{ab}|` as soon as it divides
`|N^{ab}|`, where `N = N_G(W)`.

This is the special case of the Hall–Wielandt theorem used in Peterfalvi Part II, Ch. II,
step (17) (issue 9503). -/
theorem not_dvd_card_abelianization_normalizer [Finite G] {W : Subgroup G} {P : Sylow p G}
    (hWP : W ≤ (P : Subgroup G))
    (hWZ : W ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (hwc : IsWeaklyClosed W (P : Subgroup G))
    (hG : ¬ p ∣ Nat.card (Abelianization G)) :
    ¬ p ∣ Nat.card (Abelianization ↥(Subgroup.normalizer (W : Set G))) := by
  classical
  -- `P` normalises `W`
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.le_centralizer_iff.mpr hWZ
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
    hPC.trans (Subgroup.centralizer_le_normalizer _)
  -- the focal subgroup of `P` in `G` is all of `P`
  have hPcomm : (P : Subgroup G) ≤ commutator G := sylow_le_commutator_of_not_dvd P hG
  have hfocal : (P : Subgroup G).focalSubgroup = (P : Subgroup G) := by
    rw [← Subgroup.commutator_inf_eq_focalSubgroup P]
    exact inf_eq_right.mpr hPcomm
  -- fusion is controlled by `N`
  have hcontrol : ∀ x g : G, x ∈ (P : Subgroup G) → g * x * g⁻¹ ∈ (P : Subgroup G) →
      ∃ n ∈ Subgroup.normalizer (W : Set G), g * x * g⁻¹ = n * x * n⁻¹ := by
    intro x g hx hgx
    exact exists_mem_normalizer_conj_eq hWP hWZ hwc hx hgx
  have hle := focalSubgroup_le_map_of_fusion_control hPN hcontrol
  rw [hfocal] at hle
  -- hence the Sylow subgroup of `N` lies in `⁅N, N⁆`
  set N : Subgroup G := Subgroup.normalizer (W : Set G) with hN_def
  have hPNle : (P : Subgroup G).subgroupOf N ≤ commutator ↥N := by
    intro z hz
    have hzP : (z : G) ∈ (P : Subgroup G) := Subgroup.mem_subgroupOf.mp hz
    obtain ⟨ζ, hζ, hζz⟩ := hle hzP
    have : ζ = z := Subtype.ext hζz
    rw [← this]
    exact (Subgroup.commutator_inf_eq_focalSubgroup (P.subtype hPN)).ge hζ |>.1
  exact not_dvd_card_abelianization_of_sylow_le_commutator (P.subtype hPN) hPNle

end

end OddOrder.GroupTheory
