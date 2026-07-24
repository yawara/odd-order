/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7B2_NormalJClose

/-!
# Isaacs FGT Ch.7 (Thompson subgroup) — S7B part 2 + S7C: normal-J close + Thm 7.1 proof + Thm 7.7
(pp. 209-219)
-/


namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §7C: Thompson normal p-complement proof + N/C `p'`-quotient (pp. 215-219) -/


open scoped commutatorElement

/-- centralizer ⊆ normalizer (mathlib v4.29.1 に直接の lemma 無し). -/
theorem centralizer_le_normalizer {G : Type*} [Group G] (H : Subgroup G) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer H := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hcomm : ∀ z ∈ H, z * x = x * z := Subgroup.mem_centralizer_iff.mp hx
  have hx_inv_mem : x⁻¹ ∈ Subgroup.centralizer (H : Set G) :=
    Subgroup.inv_mem _ hx
  have hcomm_inv : ∀ z ∈ H, z * x⁻¹ = x⁻¹ * z :=
    Subgroup.mem_centralizer_iff.mp hx_inv_mem
  refine ⟨fun hy => ?_, fun hxyx => ?_⟩
  · -- y ∈ H ⇒ xyx⁻¹ = y ∈ H
    have hxy : x * y = y * x := (hcomm y hy).symm
    have : x * y * x⁻¹ = y := by rw [hxy]; group
    rw [this]; exact hy
  · -- xyx⁻¹ ∈ H ⇒ y = xyx⁻¹ ∈ H
    have hcomm_z : (x * y * x⁻¹) * x⁻¹ = x⁻¹ * (x * y * x⁻¹) :=
      hcomm_inv (x * y * x⁻¹) hxyx
    -- 計算: (xyx⁻¹) * x⁻¹ = x⁻¹*(xyx⁻¹) ⇒ y = xyx⁻¹
    have h_eq : y * x⁻¹ = (x * y * x⁻¹) * x⁻¹ := by
      rw [hcomm_z]; group
    have hy_eq : y = x * y * x⁻¹ := mul_right_cancel h_eq
    rw [hy_eq]; exact hxyx

/-! **Isaacs Lem 7.7 (a)** (image of normalizer under p'-quotient).

`N ⊴ G` で `p ∤ |N|`, `P` が `G` の非自明 `p`-部分群とすると, `f := mk' N` について
`N_Ḡ(P̄) = (N_G(P)).map f`.

This is exactly Isaacs Lemma 2.17 in the quotient form needed in Ch.7. Consumers below use
`OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel` directly. -/

/-- **Isaacs Lem 7.7 (b)** (image of centralizer under p'-quotient).

`N ⊴ G` で `p ∤ |N|`, `P` が `G` の非自明 `p`-部分群とすると, `f := mk' N` について
`C_Ḡ(P̄) = (C_G(P)).map f`.

書籍 p.215-216 の証明 (Lem 2.17 の "short extension"):
1. ⊇ は明らか (image of centralizer ⊆ centralizer of image).
2. ⊆: Lem 2.17 (a) で `N̄(P̄) = (N_G(P)).map f`. `Cbar ≤ Nbar` (centralizer ≤ normalizer).
   correspondence: `X := N_G(P) ⊓ Cbar.comap f` とおく ⇒ `X.map f = Cbar`.
   `⁅P, X⁆.map f = ⁅Pbar, Cbar⁆ = ⊥` ⇒ `⁅P, X⁆ ≤ ker f = N`. かつ `⁅P, X⁆ ≤ P`
   (X ≤ N_G(P) なので). 従って `⁅P, X⁆ ≤ P ⊓ N = ⊥` (coprime), 即ち `X ≤ C_G(P)`. -/
theorem centralizer_map_of_coprime_kernel [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P) :
    Subgroup.centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.centralizer (P : Set G)).map (QuotientGroup.mk' N) := by
  classical
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  set Pbar : Subgroup (G ⧸ N) := P.map f with hPbar_def
  set Cbar : Subgroup (G ⧸ N) := Subgroup.centralizer (Pbar : Set (G ⧸ N)) with hCbar_def
  -- Coprime: P ⊓ N = ⊥
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard h_coprime_PN).eq_bot
  -- ker f = N
  have hf_ker : f.ker = N := QuotientGroup.ker_mk' N
  refine le_antisymm ?_ ?_
  · -- ⊆ direction (hard)
    -- Cbar ≤ Nbar
    have hCbar_le_Nbar : Cbar ≤ Subgroup.normalizer Pbar := centralizer_le_normalizer Pbar
    -- Nbar = (N_G(P)).map f by Lem 2.17 (a)
    have hN_eq : Subgroup.normalizer Pbar = (Subgroup.normalizer P).map f := by
      rw [hPbar_def, hf_def]
      exact OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel hp_coprime hP_pgroup
    -- X := N_G(P) ⊓ (Cbar.comap f).  X.map f = Cbar (correspondence).
    set X : Subgroup G := Subgroup.normalizer P ⊓ Cbar.comap f with hX_def
    have hX_map_eq : X.map f = Cbar := by
      apply le_antisymm
      · rintro _ ⟨y, ⟨_hy_N, hy_C⟩, rfl⟩
        exact (Subgroup.mem_comap.mp hy_C : f y ∈ Cbar)
      · intro c hc
        have hc_Nbar : c ∈ Subgroup.normalizer Pbar := hCbar_le_Nbar hc
        rw [hN_eq] at hc_Nbar
        obtain ⟨n, hn_NgP, hn_eq⟩ := hc_Nbar
        refine ⟨n, ⟨hn_NgP, ?_⟩, hn_eq⟩
        change f n ∈ Cbar
        rw [hn_eq]
        exact hc
    -- Claim: X ≤ centralizer P
    have hX_le_C : X ≤ Subgroup.centralizer (P : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      -- ⁅X, P⁆ = ⊥: ⊆ N (commutator maps to ⊥) and ⊆ P (X ≤ N_G(P)), so ⊆ P ⊓ N = ⊥.
      have h_map_bot : (⁅X, P⁆ : Subgroup G).map f = ⊥ := by
        rw [Subgroup.map_commutator, hX_map_eq]
        -- goal: ⁅Cbar, Pbar⁆ = ⊥
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
      have h_comm_le_N : (⁅X, P⁆ : Subgroup G) ≤ N := by
        rw [← hf_ker]
        exact (Subgroup.map_eq_bot_iff _).mp h_map_bot
      have h_comm_le_P : (⁅X, P⁆ : Subgroup G) ≤ P := by
        rw [Subgroup.commutator_le]
        intro x hx_X p hp_P
        -- x ∈ X ≤ N_G(P), so x p x⁻¹ ∈ P. Then ⁅x, p⁆ = x p x⁻¹ p⁻¹ ∈ P.
        have hx_N : x ∈ Subgroup.normalizer P := hx_X.1
        have hxpx : x * p * x⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp hx_N p).mp hp_P
        change x * p * x⁻¹ * p⁻¹ ∈ P
        exact P.mul_mem hxpx (P.inv_mem hp_P)
      -- ⁅X, P⁆ ≤ P ⊓ N = ⊥
      have h_comm_le_bot : (⁅X, P⁆ : Subgroup G) ≤ ⊥ := by
        have h_inf : (⁅X, P⁆ : Subgroup G) ≤ P ⊓ N := le_inf h_comm_le_P h_comm_le_N
        rw [hP_inf_N] at h_inf
        exact h_inf
      exact le_bot_iff.mp h_comm_le_bot
    -- Cbar = X.map f ⊆ (centralizer P).map f
    rw [← hX_map_eq]
    exact Subgroup.map_mono hX_le_C
  · -- ⊇ direction (easy): (C_G(P)).map f ≤ Cbar
    rintro - ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro - ⟨p, hp, rfl⟩
    -- c centralizes p in G ⇒ f(c) centralizes f(p)
    have hcp : c * p = p * c := (Subgroup.mem_centralizer_iff.mp hc p hp).symm
    rw [← map_mul, ← map_mul]
    exact congrArg f hcp.symm

/-- **Isaacs Lem 7.7** (N/C theorem for p'-quotients).

If `N ⊴ G` is a normal `p'`-subgroup and `P` is a nontrivial `p`-subgroup, then the
normalizer and centralizer of `P` commute with passage to `G/N`. -/
theorem normalizer_and_centralizer_map_of_coprime_kernel [Finite G]
    {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P) :
    (Subgroup.normalizer
        ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.normalizer P).map (QuotientGroup.mk' N)) ∧
    (Subgroup.centralizer
        ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.centralizer (P : Set G)).map (QuotientGroup.mk' N)) :=
  ⟨OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel
      hp_coprime hP_pgroup,
    centralizer_map_of_coprime_kernel hp_coprime hP_pgroup⟩

/-- Transport `OddOrder.Isaacs.Ch05.HasNormalPComplement` across a `MulEquiv`.

If `e : G ≃* H` and `G` has a normal `p`-complement, so does `H`. The complement is the
image of `G`'s complement under `e`. -/
theorem hasNormalPComplement_of_mulEquiv
    {G' H : Type*} [Group G'] [Group H]
    [Finite G'] [Finite H] {p : ℕ} [Fact p.Prime] (e : G' ≃* H)
    (hG : OddOrder.Isaacs.Ch05.HasNormalPComplement p G') :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p H := by
  classical
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  refine ⟨N.map e.toMonoidHom, ?_, ?_⟩
  · -- `N.map e` is normal in `H` because `e` is surjective.
    exact Subgroup.Normal.map hN_normal _ e.surjective
  · intro Q
    -- Pull `Q` back to a Sylow `p`-subgroup of `G'` via `e`.
    have h_range_top : (e.toMonoidHom).range = ⊤ :=
      MonoidHom.range_eq_top.mpr e.surjective
    have hQ_le_range : (Q : Subgroup H) ≤ (e.toMonoidHom).range := by
      rw [h_range_top]; exact le_top
    let Q' : Sylow p G' := Q.comapOfInjective e.toMonoidHom e.injective hQ_le_range
    have hQ'_compl : Subgroup.IsComplement' N (Q' : Subgroup G') := hN_compl Q'
    -- The image of Q' under e equals Q.
    have hQ'_eq : (Q' : Subgroup G') = (Q : Subgroup H).comap e.toMonoidHom := by
      simp [Q', Sylow.coe_comapOfInjective]
    have hQ_map : (Q' : Subgroup G').map e.toMonoidHom = (Q : Subgroup H) := by
      rw [hQ'_eq, Subgroup.map_comap_eq, h_range_top, top_inf_eq]
    -- |G'| = |H|, |N.map e| = |N|, |Q| = |Q'|.
    have hG_card : Nat.card G' = Nat.card H := Nat.card_congr e.toEquiv
    have hN_card : Nat.card (N.map e.toMonoidHom : Subgroup H) = Nat.card N := by
      exact
        (Nat.card_congr
          (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective).toEquiv).symm
    have hQ_card : Nat.card (Q : Subgroup H) = Nat.card (Q' : Subgroup G') := by
      rw [← hQ_map]
      exact
        (Nat.card_congr
          (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv).symm
    -- Multiplicativity: |N.map e| * |Q| = |H|.
    have h_card_eq :
        Nat.card N * Nat.card (Q' : Subgroup G') = Nat.card G' :=
      hQ'_compl.card_mul_card
    have h_card_H :
        Nat.card (N.map e.toMonoidHom : Subgroup H) * Nat.card (Q : Subgroup H) =
          Nat.card H := by
      rw [hN_card, hQ_card, h_card_eq, hG_card]
    -- Coprimality: |N| coprime to p (from complement in G' with p-Sylow Q').
    have hp_ndvd_N : ¬ p ∣ Nat.card N := by
      rw [← hQ'_compl.index_eq_card]; exact Q'.not_dvd_index
    obtain ⟨k, hQ'_pow⟩ := IsPGroup.iff_card.mp Q'.isPGroup'
    have hp_prime : p.Prime := Fact.out
    have h_coprime' : Nat.Coprime (Nat.card N) (Nat.card (Q' : Subgroup G')) := by
      rw [hQ'_pow]
      exact ((hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_N).symm).pow_right k
    have h_coprime :
        Nat.Coprime (Nat.card (N.map e.toMonoidHom : Subgroup H))
          (Nat.card (Q : Subgroup H)) := by
      rw [hN_card, hQ_card]; exact h_coprime'
    exact Subgroup.isComplement'_of_coprime h_card_H h_coprime

/-- Normal `p`-complements pass to quotient groups.

This is the "homomorphic images" inheritance used at the start of Isaacs §7C, before
the seven-step minimum-counterexample argument.  The complement is the quotient image
of the upstairs normal complement, and `Sylow.mapSurjective` matches each Sylow
subgroup of the quotient with the image of a Sylow subgroup upstairs. -/
theorem hasNormalPComplement_quotient
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (L : Subgroup G) [L.Normal] :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p (G ⧸ L) := by
  classical
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  let f : G →* G ⧸ L := QuotientGroup.mk' L
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective L
  refine ⟨N.map f, Subgroup.Normal.map hN_normal f hf_surj, fun Qbar => ?_⟩
  obtain ⟨Q, hQ_mapSurj⟩ := Sylow.mapSurjective_surjective (p := p) hf_surj Qbar
  have hQ_map : (Q : Subgroup G).map f = (Qbar : Subgroup (G ⧸ L)) := by
    have h := congrArg (fun R : Sylow p (G ⧸ L) => (R : Subgroup (G ⧸ L))) hQ_mapSurj
    simpa [f, Sylow.coe_mapSurjective] using h
  have hQ_compl : Subgroup.IsComplement' N (Q : Subgroup G) := hN_compl Q
  have hp_ndvd_N : ¬ p ∣ Nat.card N := by
    rw [← hQ_compl.index_eq_card]
    exact Q.not_dvd_index
  obtain ⟨k, hQ_card⟩ : ∃ k, Nat.card (Q : Subgroup G) = p ^ k :=
    IsPGroup.iff_card.mp Q.isPGroup'
  have h_coprime : Nat.Coprime (Nat.card N) (Nat.card (Q : Subgroup G)) := by
    rw [hQ_card]
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_ndvd_N).symm).pow_right k
  have h_image_compl :
      Subgroup.IsComplement' (N.map f) ((Q : Subgroup G).map f) :=
    hQ_compl.map_mk' h_coprime L
  rwa [hQ_map] at h_image_compl

/-- Normal `p`-complements pass to homomorphic images of subgroups.

This is the subgroup-image form of the inheritance principle quoted in Isaacs §7C.
It will be used for quotient images of `N_G(X)` and `C_G(X)` in Steps 2 and 3. -/
theorem hasNormalPComplement_subgroup_map
    {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (φ : G →* K) (H : Subgroup G)
    (hH : OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥H) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥(H.map φ) := by
  classical
  let φH : ↥H →* K := φ.comp H.subtype
  have hQuot : OddOrder.Isaacs.Ch05.HasNormalPComplement p (↥H ⧸ φH.ker) :=
    hasNormalPComplement_quotient (G := ↥H) hH φH.ker
  have hRange : OddOrder.Isaacs.Ch05.HasNormalPComplement p ↥φH.range :=
    hasNormalPComplement_of_mulEquiv (QuotientGroup.quotientKerEquivRange φH) hQuot
  have hRange_eq : φH.range = H.map φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.property, rfl⟩
    · rintro ⟨x, hxH, rfl⟩
      exact ⟨⟨x, hxH⟩, rfl⟩
  exact hasNormalPComplement_of_mulEquiv (MulEquiv.subgroupCongr hRange_eq) hRange

/-- If `N ⊴ G` is a normal `p'`-subgroup, then a normal `p`-complement in
`N_G(P)` pushes to a normal `p`-complement in `N_{G/N}(Pbar)`.

This combines subgroup-image inheritance with Isaacs Lemma 7.7(a). -/
theorem hasNormalPComplement_normalizer_map_of_coprime_kernel
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P)
    (hNP : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer (P : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer
        (((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)))) := by
  classical
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hImage : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥((Subgroup.normalizer P).map f) :=
    hasNormalPComplement_subgroup_map f (Subgroup.normalizer P) hNP
  have hEq :
      Subgroup.normalizer ((P.map f : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
        (Subgroup.normalizer P).map f := by
    simpa [f] using
      OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel
        hp_coprime hP_pgroup
  exact hasNormalPComplement_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hImage

/-- If `N ⊴ G` is a normal `p'`-subgroup, then a normal `p`-complement in
`C_G(P)` pushes to a normal `p`-complement in `C_{G/N}(Pbar)`.

This combines subgroup-image inheritance with Isaacs Lemma 7.7(b). -/
theorem hasNormalPComplement_centralizer_map_of_coprime_kernel
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P)
    (hCP : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.centralizer (P : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.centralizer
        (((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)))) := by
  classical
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hImage : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥((Subgroup.centralizer (P : Set G)).map f) :=
    hasNormalPComplement_subgroup_map f (Subgroup.centralizer (P : Set G)) hCP
  have hEq :
      Subgroup.centralizer ((P.map f : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
        (Subgroup.centralizer (P : Set G)).map f := by
    simpa [f] using centralizer_map_of_coprime_kernel hp_coprime hP_pgroup
  exact hasNormalPComplement_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hImage

/-- Thompson's `J` commutes with quotient by a normal `p'`-kernel on `p`-subgroups.

The quotient map is not injective on all of `G`, but it is injective on any
`p`-subgroup `P` because `P ∩ N = 1`.  This is the `J(P)` identification needed
when Steps 2 and 3 pass Thompson-normalizer hypotheses to `G/N`. -/
theorem thompsonJ_map_of_coprime_kernel
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P) :
    Subgroup.thompsonJ (P.map (QuotientGroup.mk' N)) p =
      (Subgroup.thompsonJ P p).map (QuotientGroup.mk' N) := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let qP : ↥P →* G ⧸ N := q.comp P.subtype
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard h_coprime_PN).eq_bot
  have hqP_inj : Function.Injective qP := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx_N : (x : G) ∈ N := by
      have : (x : G) ∈ (QuotientGroup.mk' N).ker := hx
      rw [QuotientGroup.ker_mk'] at this
      exact this
    have hx_inf : (x : G) ∈ P ⊓ N := ⟨x.property, hx_N⟩
    rw [hP_inf_N, Subgroup.mem_bot] at hx_inf
    exact Subtype.ext hx_inf
  have htop_qP : (⊤ : Subgroup ↥P).map qP = P.map q := by
    ext y
    constructor
    · rintro ⟨x, _hx_top, rfl⟩
      exact ⟨(x : G), x.property, rfl⟩
    · rintro ⟨x, hxP, rfl⟩
      exact ⟨⟨x, hxP⟩, trivial, rfl⟩
  have htop_subtype : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hJ_subtype :
      (Subgroup.thompsonJ (⊤ : Subgroup ↥P) p).map P.subtype =
        Subgroup.thompsonJ P p := by
    have h :=
      Subgroup.thompsonJ_map_of_injective P.subtype_injective (⊤ : Subgroup ↥P) p
    rw [htop_subtype] at h
    exact h.symm
  have hJ_qP :
      Subgroup.thompsonJ ((⊤ : Subgroup ↥P).map qP) p =
        (Subgroup.thompsonJ (⊤ : Subgroup ↥P) p).map qP :=
    Subgroup.thompsonJ_map_of_injective hqP_inj (⊤ : Subgroup ↥P) p
  change Subgroup.thompsonJ (P.map q) p = (Subgroup.thompsonJ P p).map q
  rw [← htop_qP, hJ_qP]
  change (Subgroup.thompsonJ (⊤ : Subgroup ↥P) p).map (q.comp P.subtype) =
    (Subgroup.thompsonJ P p).map q
  rw [← Subgroup.map_map, hJ_subtype]

/-- **Isaacs Thm 7.1, Step 7 reduction** (normal `J(P)` case).

This helper packages the last observation in Isaacs Step 7: once `J(P) ⊴ G`, the
normalizer `N_G(J(P))` is all of `G`, so a normal `p`-complement in that normalizer
transports across `N_G(J(P)) ≃* G`.  The public theorem below now obtains
`J(P) ⊴ G` from the real `normal_J` hypotheses instead of exposing it as the
main theorem's raw forward assumption. -/
private theorem thompson_normal_p_complement_of_thompsonJ_normal
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hNJP : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer
          ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G)))
    (hJ_normal : (Subgroup.thompsonJ (P : Subgroup G) p).Normal) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  classical
  -- J(P) ⊴ G implies N_G(J(P)) = ⊤.
  have h_norm_top :
      Subgroup.normalizer
        ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hJ_normal
  set NG : Subgroup G :=
    Subgroup.normalizer
      ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G) with hNG_def
  -- Compose ↥NG ≃* ↥⊤ ≃* G.
  let eqEquiv : NG ≃* (⊤ : Subgroup G) := MulEquiv.subgroupCongr h_norm_top
  let topToG : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  let e : ↥NG ≃* G := eqEquiv.trans topToG
  exact hasNormalPComplement_of_mulEquiv e hNJP


/-- **Isaacs Thm 7.1, Step 7** (Thompson normal `p`-complement theorem,
conditional on Steps 2-6 of the minimum-counterexample proof).

The old scaffold for this theorem assumed `J(P) ⊴ G` directly.  This version
replaces that raw forward normality hypothesis by the actual five hypotheses of
Isaacs Thm 7.6 (`normal_J`): `p ≠ 2`, `p`-separability, abelian Sylow `2`-subgroups,
`O_{p'}(G)=1`, and `C_G(Z(P)) = P`.

Thus the remaining §7C work is exactly Steps 1-6: starting from the textbook
hypotheses that `C_G(Z(P))` and `N_G(J(P))` have normal `p`-complements, the
minimum-counterexample argument must derive these normal-J hypotheses.  Once they
are available, Step 7 is now sorry-free: apply `normal_J`, so `N_G(J(P)) = G`, and
transport the normal `p`-complement from the normalizer to `G`. -/
theorem thompson_normal_p_complement
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (hNJP : OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer
          ((Subgroup.thompsonJ (P : Subgroup G) p : Subgroup G) : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  exact
    thompson_normal_p_complement_of_thompsonJ_normal P hNJP
      (normal_J P hp2 h_pSolvable h2abelian h_oPiPrime_trivial h_centralizer_center)



end OddOrder.Isaacs.Ch07
