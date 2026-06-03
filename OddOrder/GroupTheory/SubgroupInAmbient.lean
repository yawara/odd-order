/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.GroupTheory.OpResidual

/-!
# Subgroup constructions realized in the ambient group

Shared low-level `OddOrder.GroupTheory` module for two constructions that BG
(Chapters II–IV) and Peterfalvi (Sections 10–16) both need, realized as
subgroups of the *ambient* group `G` rather than of the subgroup `H`:

* `derivedInG H` — the derived subgroup `H'` of `H`, mapped back into `G`.
* `opiCoreInG π H` — the `pi`-core `O_π(H)` of `H`, mapped back into `G`.

These were originally duplicated as `BG.Ch2.S07.{derivedInG, opiCoreInG}` and as
`GroupTheory.{derivedInAmbient, piCoreIn, pCoreIn, pPrimeCoreIn}`; this file is
the single canonical home (issue 0052). It sits low in the import graph (only
`Isaacs.Ch03`) so every consumer can import it cheaply.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- **`H'` in `G`**: the derived subgroup `commutator ↥H` of a subgroup `H`,
mapped back into the ambient group `G` via `H.subtype`. -/
def derivedInG (H : Subgroup G) : Subgroup G :=
  (commutator ↥H).map H.subtype

/-- **`O_π(H)` in `G`**: the `π`-core of the subgroup `H` (largest normal
`π`-subgroup of `↥H`), mapped back into the ambient group `G` via `H.subtype`.
`opiCoreInG {p} H = O_p(H)` and `opiCoreInG {p}ᶜ H = O_{p'}(H)`, both in `G`. -/
def opiCoreInG (π : Set ℕ) (H : Subgroup G) : Subgroup G :=
  (Ch03.oPiCore π ↥H).map H.subtype

/-- `O_π(H) ≤ H` in the ambient group. -/
theorem opiCoreInG_le (π : Set ℕ) (H : Subgroup G) : opiCoreInG π H ≤ H :=
  Subgroup.map_subtype_le _

/-- The order of `opiCoreInG π H` agrees with the order of the `π`-core of `↥H`. -/
theorem card_opiCoreInG (π : Set ℕ) (H : Subgroup G) :
    Nat.card ↥(opiCoreInG π H) = Nat.card ↥(Ch03.oPiCore π ↥H) :=
  (Nat.card_congr (Subgroup.equivMapOfInjective _ H.subtype
    H.subtype_injective).toEquiv).symm

/-- `opiCoreInG π H` is a `π`-subgroup (ambient form of `oPiCore.isPiGroup`). -/
theorem isPiSubgroup_opiCoreInG [Finite G] (π : Set ℕ) (H : Subgroup G) :
    Subgroup.IsPiSubgroup π (opiCoreInG π H) := by
  intro r hr
  rw [card_opiCoreInG] at hr
  exact Ch03.oPiCore.isPiGroup π r hr

/-- A q-group is a singleton pi-subgroup. -/
theorem isPiSubgroup_singleton_of_isPGroup [Finite G] {q : ℕ} [Fact q.Prime]
    {H : Subgroup G} (hH : IsPGroup q ↥H) : Subgroup.IsPiSubgroup {q} H := by
  intro r hr
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  by_cases hn0 : n = 0
  · rw [hn, hn0, pow_zero] at hr
    simp at hr
  · rw [hn, Nat.primeFactors_prime_pow hn0 (Fact.out : q.Prime)] at hr
    simpa using hr

/-- A `{q}`-subgroup is a `q`-group. -/
theorem isPGroup_of_isPiSubgroup_singleton [Finite G] {q : ℕ} [Fact q.Prime]
    {H : Subgroup G} (hH : Subgroup.IsPiSubgroup {q} H) : IsPGroup q ↥H :=
  IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    (fun {d} hd hdvd => Set.mem_singleton_iff.mp
      (hH d (Nat.mem_primeFactors.mpr ⟨hd, hdvd, Nat.card_pos.ne'⟩))))

/-- `O_q(H)` in the ambient group is a `q`-group. -/
theorem isPGroup_opiCoreInG_singleton [Finite G] {q : ℕ} [Fact q.Prime]
    (H : Subgroup G) : IsPGroup q ↥(opiCoreInG ({q} : Set ℕ) H) :=
  isPGroup_of_isPiSubgroup_singleton (isPiSubgroup_opiCoreInG ({q} : Set ℕ) H)

/-- If `N ≤ H` is normal in `H` and is a `π`-subgroup, then it lies in the
ambient realization of `O_π(H)`. -/
theorem le_opiCoreInG_of_normal_of_isPiSubgroup {π : Set ℕ} {H N : Subgroup G}
    (hNH : N ≤ H) (hNnorm : (N.subgroupOf H).Normal)
    (hNpi : Subgroup.IsPiSubgroup π N) :
    N ≤ opiCoreInG π H := by
  haveI := hNnorm
  have hNpi_sub : Ch03.Subgroup.IsPiGroup π (N.subgroupOf H) := by
    intro r hr
    refine hNpi r ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv] at hr
  calc N = (N.subgroupOf H).map H.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hNH).symm
    _ ≤ (Ch03.oPiCore π ↥H).map H.subtype :=
        Subgroup.map_mono (Ch03.Subgroup.IsPiGroup.le_oPiCore hNpi_sub)
    _ = opiCoreInG π H := rfl

/-- **`H` normalizes `O_π(H)`** (in the ambient group): the `π`-core is characteristic
in `↥H`, so conjugation by an element of `H` (which restricts to an automorphism of
`↥H`) fixes its image in `G`. -/
theorem le_normalizer_opiCoreInG (π : Set ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (opiCoreInG π H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hfix := Subgroup.characteristic_iff_comap_eq.mp
    (Ch03.oPiCore.characteristic π ↥H) (MulAut.conj (⟨x, hx⟩ : ↥H))
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨MulAut.conj (⟨x, hx⟩ : ↥H) z, ?_, rfl⟩
    have h1 : z ∈ (Ch03.oPiCore π ↥H).comap
        (MulAut.conj (⟨x, hx⟩ : ↥H)).toMonoidHom := by
      rw [hfix]
      exact hz
    exact Subgroup.mem_comap.mp h1
  · intro hy
    obtain ⟨z, hz, hz_eq⟩ := hy
    have hy_mem : y ∈ H := by
      have hyH : x * y * x⁻¹ ∈ H := hz_eq ▸ z.2
      have h1 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      rw [← h1]
      exact H.mul_mem (H.mul_mem (H.inv_mem hx) hyH) hx
    have hzy : z = MulAut.conj (⟨x, hx⟩ : ↥H) (⟨y, hy_mem⟩ : ↥H) := by
      apply Subtype.ext
      simpa [MulAut.conj_apply] using hz_eq
    have h2 : (⟨y, hy_mem⟩ : ↥H) ∈ (Ch03.oPiCore π ↥H).comap
        (MulAut.conj (⟨x, hx⟩ : ↥H)).toMonoidHom := by
      rw [Subgroup.mem_comap]
      rw [hzy] at hz
      exact hz
    rw [hfix] at h2
    exact ⟨⟨y, hy_mem⟩, h2, rfl⟩


/-- Any subgroup normalizing `H` also normalizes the ambient realization of `O_π(H)`. -/
theorem le_normalizer_opiCoreInG_of_le_normalizer (π : Set ℕ) {A H : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) :
    A ≤ Subgroup.normalizer (opiCoreInG π H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxH : x ∈ Subgroup.normalizer (H : Set G) := hAH hx
  let ψ : MulAut ↥H := H.normalizerMonoidHom ⟨x, hxH⟩
  have hfix := Subgroup.characteristic_iff_comap_eq.mp
    (Ch03.oPiCore.characteristic π ↥H) ψ
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨ψ z, ?_, ?_⟩
    · have hzCore : z ∈ (Ch03.oPiCore π ↥H).comap ψ.toMonoidHom := by
        rw [hfix]
        exact hz
      exact Subgroup.mem_comap.mp hzCore
    · change ↑(ψ z) = x * ↑z * x⁻¹
      rfl
  · intro hy
    obtain ⟨z, hz, hz_eq⟩ := hy
    have hyH : y ∈ H :=
      (Subgroup.mem_normalizer_iff.mp hxH y).mpr (hz_eq ▸ z.2)
    have hzy : z = (MulEquiv.toMonoidHom ψ) ⟨y, hyH⟩ := by
      apply Subtype.ext
      change (z : G) = x * y * x⁻¹
      exact hz_eq
    have hyCore : (⟨y, hyH⟩ : ↥H) ∈ (Ch03.oPiCore π ↥H).comap ψ.toMonoidHom := by
      rw [Subgroup.mem_comap]
      rw [← hzy]
      exact hz
    rw [hfix] at hyCore
    exact ⟨⟨y, hyH⟩, hyCore, rfl⟩

end OddOrder.GroupTheory
