/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch02_Subnormality.Basic

/-!
# Theorem211Wielandt

Prefix-split from `OddOrder.Isaacs.Ch02_Subnormality.Main` (2000-line limit, issue 0103 第 2 パス).
-/
open OddOrder.Isaacs.Ch01

namespace OddOrder.Isaacs.Ch02
section /- 2A: Subnormality basics, joins, Wielandt's F(G) (pp. 45-54) -/
variable {G : Type*} [Group G]

variable (G) in

/-! ### Isaacs Thm 2.11 (Wielandt abelian-in-F(G)) -/

open scoped Pointwise in
/-- **古典的計数公式** `|H · K| · |H ∩ K| = |H| · |K|` (group counting formula).
有限群 `G` の部分群 `H, K` の **集合積** の cardinality と intersection の cardinality
が, `H`, `K` の cardinality の積に等しい. mathlib 未収載なので, ここで一度示しておく.

証明: H を G/K (左 coset 集合) に左乗法で作用させ, `(1 : G ⧸ K)` の軌道が
`(H : Set G).image (↑ : G → G ⧸ K)`, 安定化群が `K.subgroupOf H` (≃ `H ⊓ K`).
orbit-stabilizer + `Subgroup.card_mul_eq_card_subgroup_mul_card_quotient` で合成.

Thm 2.11 (Wielandt) と Cor 2.19 で `H = K = A` (またはその共役) の形で使う. -/
lemma card_set_mul_card_inf {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) :
    Nat.card ((H : Set G) * (K : Set G)) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  classical
  have h1 : Nat.card ((H : Set G) * (K : Set G)) =
      Nat.card ↥K * Nat.card ((H : Set G).image ((↑) : G → G ⧸ K)) :=
    Subgroup.card_mul_eq_card_subgroup_mul_card_quotient K (H : Set G)
  have h_orbit_eq : (MulAction.orbit (↥H) (((1 : G) : G ⧸ K))) =
      (H : Set G).image ((↑) : G → G ⧸ K) := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨(h : G), h.2, ?_⟩
      change ((h : G) : G ⧸ K) = (((h : G) : G) * (1 : G) : G ⧸ K)
      rw [mul_one]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, by
        change ((⟨g, hg⟩ : ↥H).val * (1 : G) : G ⧸ K) = ((g : G) : G ⧸ K)
        rw [mul_one]⟩
  have h_stab_eq : MulAction.stabilizer ↥H (((1 : G) : G ⧸ K)) = K.subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hsmul
      have hraw : (((h : G) : G) * (1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := hsmul
      rw [mul_one] at hraw
      have := QuotientGroup.eq.mp hraw
      simpa using this
    · intro hh
      change (((h : G) : G) * (1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K)
      rw [mul_one]
      apply QuotientGroup.eq.mpr
      simpa using hh
  have h_orbstab : Nat.card (MulAction.orbit ↥H (((1 : G) : G ⧸ K))) *
      Nat.card (MulAction.stabilizer ↥H (((1 : G) : G ⧸ K))) = Nat.card ↥H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥H _)
  have h_subgrpof_card : Nat.card ↥(K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
    rw [show K.subgroupOf H = (H ⊓ K).subgroupOf H from
      (Subgroup.inf_subgroupOf_left K H).symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h_orbit_eq, h_stab_eq, h_subgrpof_card] at h_orbstab
  rw [h1, mul_assoc, h_orbstab, mul_comm]

open scoped Pointwise in
/-- **Isaacs Thm 2.11** (Wielandt abelian-in-F(G)) の `|G|`-induction 補助補題. -/
private theorem subset_fitting_aux : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {A : Subgroup G},
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ H : Subgroup G, A ≤ H →
        ((A.subgroupOf H).index) ^ 2 ≤ (Subgroup.center ↥H).index) →
      A ≤ fitting G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hcard A _ _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ hGcard A hAab h
    classical
    -- A is nilpotent (abelian).
    have hA_center_top : Subgroup.center ↥A = ⊤ := by
      ext ⟨x, hx⟩
      refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
      rw [Subgroup.mem_center_iff]
      intro ⟨g, hg⟩
      exact Subtype.ext (hAab g hg x hx)
    haveI hA_nilp : Group.IsNilpotent ↥A := ⟨1, by
      rw [Subgroup.upperCentralSeries_one]; exact hA_center_top⟩
    -- Case split: A subnormal in G.
    by_cases hA_sn : A.IsSubnormal
    · exact (le_fitting_iff_isNilpotent_and_isSubnormal A).mpr ⟨hA_nilp, hA_sn⟩
    -- Case: A not subnormal. Derive contradiction.
    exfalso
    -- IH gives `A.subgroupOf K` subnormal in K for every proper K ⊇ A.
    have hAK_sn : ∀ K : Subgroup G, A ≤ K → K ≠ ⊤ → (A.subgroupOf K).IsSubnormal := by
      intro K hAK hKne
      haveI : Finite K := inferInstance
      have hKcard : Nat.card K ≤ n := by
        have hKlt_card : Nat.card K < Nat.card G := by
          have hKlag := K.card_mul_index
          have h1 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
          have h2 : K.index ≠ 1 := fun he => hKne (Subgroup.index_eq_one.mp he)
          have hKidx : K.index ≥ 2 := by omega
          have hKpos : 0 < Nat.card K := Nat.card_pos
          nlinarith
        omega
      -- Inherited abelianness of A.subgroupOf K.
      have hAK_ab : ∀ a ∈ A.subgroupOf K, ∀ b ∈ A.subgroupOf K, a * b = b * a := by
        intro a ha b hb
        rw [Subgroup.mem_subgroupOf] at ha hb
        exact Subtype.ext (hAab _ ha _ hb)
      -- Inherited index hypothesis: for H' ⊇ A.subgroupOf K in K, transfer h on H'.map K.subtype.
      have hAK_h : ∀ H' : Subgroup ↥K, A.subgroupOf K ≤ H' →
          (((A.subgroupOf K).subgroupOf H').index) ^ 2 ≤ (Subgroup.center ↥H').index := by
        intro H' hAH'
        set H : Subgroup G := H'.map K.subtype with hH_def
        have hAH : A ≤ H := by
          intro a ha
          have haK : a ∈ K := hAK ha
          exact ⟨⟨a, haK⟩, hAH' ((Subgroup.mem_subgroupOf).mpr ha), rfl⟩
        have hkey := h H hAH
        -- Iso φ : H' ≃* H (= H'.map K.subtype).
        set φ : ↥H' ≃* ↥H :=
          Subgroup.equivMapOfInjective H' K.subtype K.subtype_injective with hφ_def
        have hφ_surj : Function.Surjective (φ.toMonoidHom) := φ.surjective
        -- Subgroup correspondence:
        -- (A.subgroupOf H).comap φ.toMonoidHom = (A.subgroupOf K).subgroupOf H'.
        have h_S_eq : (A.subgroupOf H).comap φ.toMonoidHom =
            (A.subgroupOf K).subgroupOf H' := by
          ext x
          rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
              Subgroup.mem_subgroupOf]
          rfl
        -- Index transfer for A.
        have h_idx_S : ((A.subgroupOf K).subgroupOf H').index =
            (A.subgroupOf H).index := by
          rw [← h_S_eq]
          exact (A.subgroupOf H).index_comap_of_surjective hφ_surj
        -- Center correspondence via iso.
        have h_C_eq : (Subgroup.center ↥H).comap φ.toMonoidHom = Subgroup.center ↥H' := by
          ext x
          rw [Subgroup.mem_comap, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
          constructor
          · intro hx y
            apply φ.injective
            change φ.toMonoidHom (y * x) = φ.toMonoidHom (x * y)
            rw [map_mul, map_mul]
            exact hx (φ.toMonoidHom y)
          · intro hx z
            obtain ⟨y, hy⟩ := hφ_surj z
            calc z * φ.toMonoidHom x = φ.toMonoidHom y * φ.toMonoidHom x := by rw [← hy]
              _ = φ.toMonoidHom (y * x) := (map_mul _ _ _).symm
              _ = φ.toMonoidHom (x * y) := by rw [hx y]
              _ = φ.toMonoidHom x * φ.toMonoidHom y := map_mul _ _ _
              _ = φ.toMonoidHom x * z := by rw [hy]
        have h_idx_C : (Subgroup.center ↥H').index = (Subgroup.center ↥H).index := by
          rw [← h_C_eq]
          exact (Subgroup.center ↥H).index_comap_of_surjective hφ_surj
        rw [h_idx_S, h_idx_C]
        exact hkey
      have hAK_le_F : A.subgroupOf K ≤ fitting ↥K := ih ↥K hKcard hAK_ab hAK_h
      -- F(K) nilpotent (Cor 1.28(a) instance), A.subgroupOf K ≤ F(K) subnormal in F(K).
      have hAK_in_FK : ((A.subgroupOf K).subgroupOf (fitting ↥K)).IsSubnormal :=
        isSubnormal_of_isNilpotent_finite _
      have hFK_sn : (fitting ↥K).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
      exact Subgroup.IsSubnormal.trans hAK_le_F hAK_in_FK hFK_sn
    -- Zipper Lemma.
    obtain ⟨M, hMcoatom, hAM, hMuniq⟩ := zipper_lemma hAK_sn hA_sn
    -- A ≠ ⊤ (else A ⊴⊴ G via top).
    have h_A_ne_top : A ≠ ⊤ := by
      intro hAtop
      apply hMcoatom.1
      exact le_top.antisymm (hAtop ▸ hAM)
    -- Show ∃ g, ⟨A, (MulAut.conj g) • A⟩ = ⊤.
    have h_exists_g : ∃ g : G, A ⊔ ((MulAut.conj g) • A : Subgroup G) = ⊤ := by
      by_contra h_all_proper
      push Not at h_all_proper
      -- ∀ g, A ⊔ A^g < ⊤, hence ≤ some maximal = M.
      have hAg_le_M : ∀ g : G, ((MulAut.conj g) • A : Subgroup G) ≤ M := by
        intro g
        have hne : A ⊔ ((MulAut.conj g) • A : Subgroup G) ≠ ⊤ := h_all_proper g
        obtain ⟨K, hKcoatom, hKle⟩ :=
          (eq_top_or_exists_le_coatom (A ⊔ ((MulAut.conj g) • A : Subgroup G))).resolve_left hne
        have hAK : A ≤ K := le_sup_left.trans hKle
        have hKM : K = M := hMuniq K hKcoatom hAK
        exact (le_sup_right.trans hKle).trans hKM.le
      -- A^G (normal closure) ≤ M.
      have hNH_le_M : Subgroup.normalClosure (A : Set G) ≤ M := by
        rw [Subgroup.normalClosure, Subgroup.closure_le]
        intro y hy
        rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨a, haA, hConj⟩
        rcases hConj with ⟨c, hc⟩
        apply hAg_le_M (c : G)
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def]
        change ((c : G)⁻¹) * y * ((c : G)⁻¹)⁻¹ ∈ A
        rw [inv_inv]
        have hc_eq : (c : G) * a = y * (c : G) := hc
        have ha_eq : ((c : G)⁻¹) * y * ((c : G)) = a := by
          rw [mul_assoc, ← hc_eq]
          group
        rw [ha_eq]; exact haA
      have hNH_lt : Subgroup.normalClosure (A : Set G) ≠ ⊤ := fun hNHtop =>
        hMcoatom.1 (le_top.antisymm (hNHtop.symm.le.trans hNH_le_M))
      -- A ⊴⊴ A^G ⊴ G ⇒ A ⊴⊴ G, contradiction.
      have hA_le_NH : A ≤ Subgroup.normalClosure (A : Set G) := Subgroup.le_normalClosure
      have hA_sn_NH : (A.subgroupOf (Subgroup.normalClosure (A : Set G))).IsSubnormal :=
        hAK_sn _ hA_le_NH hNH_lt
      have hNH_normal_sn : (Subgroup.normalClosure (A : Set G)).IsSubnormal :=
        Subgroup.Normal.isSubnormal inferInstance
      exact hA_sn (Subgroup.IsSubnormal.trans hA_le_NH hA_sn_NH hNH_normal_sn)
    obtain ⟨g, hsup_top⟩ := h_exists_g
    -- Helper: A^g is abelian. For b₁, b₂ ∈ A^g, write back via g⁻¹.
    have hAg_ab : ∀ b₁ ∈ ((MulAut.conj g) • A : Subgroup G),
        ∀ b₂ ∈ ((MulAut.conj g) • A : Subgroup G), b₁ * b₂ = b₂ * b₁ := by
      intro b₁ hb₁ b₂ hb₂
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def] at hb₁ hb₂
      have hb₁' : g⁻¹ * b₁ * g ∈ A := by
        have : g⁻¹ * b₁ * (g⁻¹)⁻¹ ∈ A := hb₁
        rwa [inv_inv] at this
      have hb₂' : g⁻¹ * b₂ * g ∈ A := by
        have : g⁻¹ * b₂ * (g⁻¹)⁻¹ ∈ A := hb₂
        rwa [inv_inv] at this
      have habelian := hAab _ hb₁' _ hb₂'
      -- (g⁻¹ b₁ g)(g⁻¹ b₂ g) = g⁻¹ (b₁ b₂) g, similarly for swap. Cancel.
      have hs1 : (g⁻¹ * b₁ * g) * (g⁻¹ * b₂ * g) = g⁻¹ * (b₁ * b₂) * g := by group
      have hs2 : (g⁻¹ * b₂ * g) * (g⁻¹ * b₁ * g) = g⁻¹ * (b₂ * b₁) * g := by group
      rw [hs1, hs2] at habelian
      -- conjugate both sides by g to cancel.
      have := congrArg (fun z => g * z * g⁻¹) habelian
      calc b₁ * b₂ = g * (g⁻¹ * (b₁ * b₂) * g) * g⁻¹ := by group
        _ = g * (g⁻¹ * (b₂ * b₁) * g) * g⁻¹ := this
        _ = b₂ * b₁ := by group
    -- A ⊓ A^g ⊆ Z(G): For c ∈ A ⊓ A^g, show centralizer contains both A and A^g, hence ⊤.
    have h_inf_center : (A ⊓ ((MulAut.conj g) • A : Subgroup G) : Subgroup G) ≤
        Subgroup.center G := by
      intro c hc
      rw [Subgroup.mem_inf] at hc
      obtain ⟨hc_A, hc_Ag⟩ := hc
      rw [Subgroup.mem_center_iff]
      intro x
      -- Show centralizer of {c} contains A and A^g, hence ⊤ ≤ centralizer.
      have h_central_A : A ≤ Subgroup.centralizer ({c} : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hAab a ha c hc_A).symm
      have h_central_Ag : ((MulAut.conj g) • A : Subgroup G) ≤
          Subgroup.centralizer ({c} : Set G) := by
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hAg_ab b hb c hc_Ag).symm
      have h_sup_le : (A ⊔ ((MulAut.conj g) • A : Subgroup G) : Subgroup G) ≤
          Subgroup.centralizer ({c} : Set G) := sup_le h_central_A h_central_Ag
      have h_central_top : Subgroup.centralizer ({c} : Set G) = ⊤ :=
        top_le_iff.mp (hsup_top ▸ h_sup_le)
      have hx_central : x ∈ Subgroup.centralizer ({c} : Set G) := by
        rw [h_central_top]; exact Subgroup.mem_top x
      rw [Subgroup.mem_centralizer_iff] at hx_central
      exact (hx_central c (Set.mem_singleton _)).symm
    -- Counting: |A·A^g| · |A⊓A^g| = |A|² (via card_set_mul_card_inf).
    have h_count_eq : Nat.card ((A : Set G) *
        (((MulAut.conj g) • A : Subgroup G) : Set G)) *
        Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) =
        Nat.card ↥A * Nat.card ↥((MulAut.conj g) • A : Subgroup G) :=
      card_set_mul_card_inf A ((MulAut.conj g) • A)
    have h_conj_card : Nat.card ↥((MulAut.conj g) • A : Subgroup G) = Nat.card ↥A := by
      rw [Subgroup.pointwise_smul_def]
      exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))
    rw [h_conj_card] at h_count_eq
    -- |A·A^g| < |G| (Lemma 2.10 対偶).
    have h_set_mul_lt : Nat.card ((A : Set G) *
        (((MulAut.conj g) • A : Subgroup G) : Set G)) < Nat.card G := by
      have h_subset : (A : Set G) *
          (((MulAut.conj g) • A : Subgroup G) : Set G) ⊆ Set.univ := Set.subset_univ _
      have h_set_ne_univ : (A : Set G) *
          (((MulAut.conj g) • A : Subgroup G) : Set G) ≠ Set.univ := by
        intro h_univ
        apply h_A_ne_top
        apply eq_top_of_set_mul_conj_eq_top g⁻¹
        convert h_univ using 2
        rw [inv_inv]
      -- |set| ≤ |G|, and |set| ≠ |G| (else set = univ).
      have h_card_le : Nat.card ((A : Set G) *
          (((MulAut.conj g) • A : Subgroup G) : Set G)) ≤ Nat.card G := by
        rw [← Nat.card_univ (α := G)]
        refine Nat.card_le_card_of_injective (fun x => ⟨x.val, Set.mem_univ _⟩) ?_
        intro x y hxy
        exact Subtype.ext (Subtype.mk.injEq _ _ _ _ |>.mp hxy)
      rcases lt_or_eq_of_le h_card_le with hlt | heq
      · exact hlt
      · exfalso
        apply h_set_ne_univ
        apply Set.eq_of_subset_of_ncard_le h_subset _ Set.finite_univ
        rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
        exact le_of_eq heq.symm
    -- |A⊓A^g| ≤ |Z(G)|.
    have h_inf_le_center_card : Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) ≤
        Nat.card ↥(Subgroup.center G) :=
      Subgroup.card_le_of_le h_inf_center
    -- Counting: derive |G| · |Z(G)| > |A|² .
    have h_card_inf_pos : 0 < Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) := Nat.card_pos
    have h_card_A_pos : 0 < Nat.card ↥A := Nat.card_pos
    have h_card_G_pos : 0 < Nat.card G := Nat.card_pos
    have h_count_lt : Nat.card G * Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) >
        Nat.card ↥A * Nat.card ↥A := by
      have h1 : Nat.card ((A : Set G) *
          (((MulAut.conj g) • A : Subgroup G) : Set G)) *
          Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) <
          Nat.card G * Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) :=
        (Nat.mul_lt_mul_right h_card_inf_pos).mpr h_set_mul_lt
      omega
    have h_G_center_gt : Nat.card G * Nat.card ↥(Subgroup.center G) >
        Nat.card ↥A * Nat.card ↥A := by
      calc Nat.card G * Nat.card ↥(Subgroup.center G)
          ≥ Nat.card G * Nat.card ↥(A ⊓ (MulAut.conj g) • A : Subgroup G) :=
            Nat.mul_le_mul_left _ h_inf_le_center_card
        _ > Nat.card ↥A * Nat.card ↥A := h_count_lt
    -- Apply h at H = ⊤: convert to A.index^2 ≤ (center G).index.
    have h_at_top := h ⊤ le_top
    -- h_at_top : (A.subgroupOf ⊤).index ^ 2 ≤ (Subgroup.center ↥(⊤ : Subgroup G)).index
    -- Conversion 1: (A.subgroupOf ⊤).index = A.index.
    have h_idx_A : (A.subgroupOf ⊤).index = A.index := A.relIndex_top_right
    -- Conversion 2: (center ↥⊤).index = (center G).index, via topEquiv.
    have h_topEquiv_surj : Function.Surjective
        ((Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).toMonoidHom) :=
      (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).surjective
    have h_idx_C : (Subgroup.center ↥(⊤ : Subgroup G)).index = (Subgroup.center G).index := by
      have hcenter_eq : (Subgroup.center G).comap
          (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).toMonoidHom =
          Subgroup.center ↥(⊤ : Subgroup G) := by
        ext x
        rw [Subgroup.mem_comap, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
        constructor
        · intro hx y
          apply Subgroup.topEquiv.injective
          change Subgroup.topEquiv.toMonoidHom (y * x) = Subgroup.topEquiv.toMonoidHom (x * y)
          rw [map_mul, map_mul]
          exact hx (Subgroup.topEquiv.toMonoidHom y)
        · intro hx z
          obtain ⟨y, hy⟩ := h_topEquiv_surj z
          calc z * Subgroup.topEquiv.toMonoidHom x
              = Subgroup.topEquiv.toMonoidHom y * Subgroup.topEquiv.toMonoidHom x := by rw [← hy]
            _ = Subgroup.topEquiv.toMonoidHom (y * x) := (map_mul _ _ _).symm
            _ = Subgroup.topEquiv.toMonoidHom (x * y) := by rw [hx y]
            _ = Subgroup.topEquiv.toMonoidHom x * Subgroup.topEquiv.toMonoidHom y := map_mul _ _ _
            _ = Subgroup.topEquiv.toMonoidHom x * z := by rw [hy]
      rw [← hcenter_eq]
      exact (Subgroup.center G).index_comap_of_surjective h_topEquiv_surj
    rw [h_idx_A, h_idx_C] at h_at_top
    -- Numerical derivation: from h_at_top + h_G_center_gt, contradiction.
    -- h_at_top : A.index ^ 2 ≤ (Subgroup.center G).index
    -- hA_lag : A.index * |A| = |G|
    -- hC_lag : (Subgroup.center G).index * |Z(G)| = |G|
    -- h_G_center_gt : |G| * |Z(G)| > |A| * |A|
    -- Derivation: |G|^2 * |Z(G)| = A.index^2 * |A|^2 * |Z(G)| ≤ (center G).index * |A|^2 * |Z(G)|
    --   = ((center G).index * |Z(G)|) * |A|^2 = |G| * |A|^2.
    -- So |G|^2 * |Z(G)| ≤ |G| * |A|^2, cancel |G|: |G| * |Z(G)| ≤ |A|^2.
    -- Contradicts h_G_center_gt.
    have hA_lag : A.index * Nat.card ↥A = Nat.card G := A.index_mul_card
    have hC_lag : (Subgroup.center G).index * Nat.card ↥(Subgroup.center G) = Nat.card G :=
      (Subgroup.center G).index_mul_card
    -- |G|^2 = A.index^2 * |A|^2.
    have hGG_eq : Nat.card G * Nat.card G =
        A.index ^ 2 * (Nat.card ↥A * Nat.card ↥A) := by
      have h := hA_lag
      calc Nat.card G * Nat.card G
          = (A.index * Nat.card ↥A) * (A.index * Nat.card ↥A) := by rw [h]
        _ = A.index ^ 2 * (Nat.card ↥A * Nat.card ↥A) := by ring
    -- Step: A.index^2 * |A|^2 * |Z(G)| ≤ (center G).index * |A|^2 * |Z(G)| = |G| * |A|^2.
    have h_step : Nat.card G * Nat.card G * Nat.card ↥(Subgroup.center G) ≤
        Nat.card G * (Nat.card ↥A * Nat.card ↥A) := by
      calc Nat.card G * Nat.card G * Nat.card ↥(Subgroup.center G)
          = A.index ^ 2 * (Nat.card ↥A * Nat.card ↥A) * Nat.card ↥(Subgroup.center G) := by
            rw [hGG_eq]
        _ ≤ (Subgroup.center G).index * (Nat.card ↥A * Nat.card ↥A) *
              Nat.card ↥(Subgroup.center G) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h_at_top)
        _ = ((Subgroup.center G).index * Nat.card ↥(Subgroup.center G)) *
              (Nat.card ↥A * Nat.card ↥A) := by ring
        _ = Nat.card G * (Nat.card ↥A * Nat.card ↥A) := by rw [hC_lag]
    -- Cancel |G| > 0.
    have h_GZ_le : Nat.card G * Nat.card ↥(Subgroup.center G) ≤
        Nat.card ↥A * Nat.card ↥A := by
      have h_pos := Nat.card_pos (α := G)
      have h_eq : Nat.card G * (Nat.card G * Nat.card ↥(Subgroup.center G)) ≤
          Nat.card G * (Nat.card ↥A * Nat.card ↥A) := by
        calc Nat.card G * (Nat.card G * Nat.card ↥(Subgroup.center G))
            = Nat.card G * Nat.card G * Nat.card ↥(Subgroup.center G) := by ring
          _ ≤ Nat.card G * (Nat.card ↥A * Nat.card ↥A) := h_step
      exact Nat.le_of_mul_le_mul_left h_eq h_pos
    -- Contradiction.
    omega

/-- **Isaacs Thm 2.11** (Wielandt abelian-in-F(G)). 有限群 `G` の abelian 部分群 `A`
で, 全ての `H ⊇ A` について `|H:A|² ≤ |H:Z(H)|` ならば `A ≤ F(G)`.

書籍 p.50 の証明 (`|G|`-induction; cf. Wielandt 1958):
1. **IH**: 任意の真部分群 `H ⊋ A` で `A ≤ F(H)` ⇒ `A ⊴⊴ H` (Thm 2.2 経由).
2. **Zipper Lemma (2.9)** で, `A` が `G` で部分正規でないなら `A` を含む極大 `M` が一意.
3. ある `g ∈ G` で `⟨A, A^g⟩ = G`: 全 `g` で `⟨A, A^g⟩ < G` なら `A^g ⊆ M` 故 `A^G ⊆ M < G`,
   `A ⊴ A^G ⊴ G` で `A ⊴⊴ G`, 矛盾.
4. `A, A^g` abelian で `⟨A, A^g⟩ = G` ⇒ `A ⊓ A^g ⊆ Z(G)`.
5. Lemma 2.10 で `|A · A^g| < |G|`. 計数 `|A·A^g| = |A|²/|A⊓A^g| ≥ |A|²/|Z(G)|`
   で `|G:A|² > |G:Z(G)|`, 仮定 (`H = G`) に矛盾. -/
theorem subset_fitting_of_index_sq_le_index_center [Finite G] {A : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h : ∀ H : Subgroup G, A ≤ H →
      ((A.subgroupOf H).index) ^ 2 ≤ (Subgroup.center ↥H).index) :
    A ≤ fitting G :=
  subset_fitting_aux (Nat.card G) G le_rfl hAab h

end -- 2A

section /- 2B: Baer's theorem (pp. 55-58) -/

variable {G : Type*} [Group G]

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** — 順方向: `H ≤ F(G)` ⇒ ∀x, `⟨H, H^x⟩` 冪零.

`H, H^x ⊆ F(G)` (F(G) ⊴ G で `H^x ⊆ F(G)`), `⟨H, H^x⟩ = H ⊔ H^x ≤ F(G)`,
F(G) 冪零, subgroup of nilpotent も冪零. -/
theorem baer_sup_conj_isNilpotent_of_le_fitting [Finite G] {H : Subgroup G}
    (hH : H ≤ fitting G) (x : G) :
    Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G)) := by
  -- MulAut.conj x • F(G) = F(G) (F(G) ⊴ G).
  have hFnormal : (MulAut.conj x : MulAut G) • (fitting G : Subgroup G) = fitting G :=
    Subgroup.Normal.conj_smul_eq_self (h := fitting.normal G) x (fitting G)
  -- H^x ≤ F(G).
  have hHx_le : ((MulAut.conj x) • H : Subgroup G) ≤ fitting G := by
    rw [← hFnormal]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hH
  -- H ⊔ H^x ≤ F(G).
  have hSup_le : (H ⊔ ((MulAut.conj x) • H : Subgroup G)) ≤ fitting G := sup_le hH hHx_le
  -- Subgroup of nilpotent F(G) is nilpotent.
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSup_le)

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** 逆方向の `|G|`-induction の generalized core.

任意の有限群 `G` (with `Nat.card G ≤ n`) について,
`∀x ∈ G, ⟨H, H^x⟩ 冪零` ならば `H ≤ F(G)`.

Isaacs p.55 の証明戦略:
1. `x = 1` 適用で `H` 自身が冪零.
2. Thm 2.2 で `H ≤ F(G) ⟺ H 冪零 ∧ H 部分正規`. 部分正規性のみ示せばよい.
3. 部分正規性を背理法 + `|G|`-induction.  IH が真部分群 `K ⊇ H` で `H` の部分正規性を
   与える (Zipper Lemma の hypothesis を充足).
4. Zipper Lemma で `H` を含む極大 `M` 一意.
5. 各 `x` で `⟨H, H^x⟩` 冪零 ≠ ⊤ (= ⊤ なら `G` 冪零 ⇒ 矛盾) ⇒ `⟨H, H^x⟩ ⊆ M`.
6. 正規閉包 `H^G ⊆ M < ⊤`. IH で `H ⊴⊴ H^G ⊴ G`, 矛盾. -/
private theorem le_fitting_of_baer_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {H : Subgroup G},
      (∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G))) →
      H ≤ fitting G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ H hN
    -- Step 0: H は冪零 (x = 1 で hN 適用).
    have hH_nilp : Group.IsNilpotent ↥H := by
      have h1 := hN 1
      rw [map_one, one_smul, sup_idem] at h1
      exact h1
    -- Step 1: H が部分正規であれば Thm 2.2 で結論.
    suffices hSn : H.IsSubnormal from
      (le_fitting_iff_isNilpotent_and_isSubnormal H).mpr ⟨hH_nilp, hSn⟩
    -- Step 2: H 部分正規でないと仮定 ⇒ 矛盾.
    by_contra hSnneg
    -- IH: 真部分群 K ⊇ H で H.subgroupOf K は部分正規.
    have hIH : ∀ K : Subgroup G, H ≤ K → K ≠ ⊤ →
        (H.subgroupOf K).IsSubnormal := by
      intro K hHK hKne
      have hK_card : Nat.card K ≤ n := by
        have hKle : Nat.card K ≤ Nat.card G := K.card_le_card_group
        have hKne_card : Nat.card K ≠ Nat.card G := fun heq =>
          hKne (Subgroup.eq_top_of_card_eq K heq)
        omega
      have hIH_K : (H.subgroupOf K) ≤ fitting K := by
        apply ih K hK_card
        intro y
        -- Permutability transfer G → ↥K via Subgroup.conj_smul_subgroupOf.
        rw [Subgroup.conj_smul_subgroupOf hHK]
        have hHy_le_K : ((MulAut.conj (y : G)) • H : Subgroup G) ≤ K :=
          Subgroup.conj_smul_le_of_le hHK y
        rw [← Subgroup.subgroupOf_sup hHK hHy_le_K]
        haveI : Group.IsNilpotent
            ↥(H ⊔ ((MulAut.conj (y : G)) • H) : Subgroup G) := hN (y : G)
        have hsup_le_K : (H ⊔ ((MulAut.conj (y : G)) • H) : Subgroup G) ≤ K :=
          sup_le hHK hHy_le_K
        exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hsup_le_K).symm
      exact ((le_fitting_iff_isNilpotent_and_isSubnormal _).mp hIH_K).2
    -- Zipper Lemma で `H` を含む極大部分群 `M` の一意性.
    obtain ⟨M, hMcoatom, _, hMuniq⟩ := zipper_lemma hIH hSnneg
    -- 各 x : G で `MulAut.conj x • H ≤ M`.
    have hHx_le_M : ∀ x : G, ((MulAut.conj x) • H : Subgroup G) ≤ M := by
      intro x
      have hNx := hN x
      -- ⟨H, H^x⟩ ≠ ⊤ (else G 冪零 ⇒ H 部分正規, 矛盾).
      have hsup_ne_top : (H ⊔ ((MulAut.conj x) • H : Subgroup G)) ≠ ⊤ := by
        intro h_top
        apply hSnneg
        rw [h_top] at hNx
        haveI := hNx
        haveI hG_nilp : Group.IsNilpotent G :=
          Group.nilpotent_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
        exact isSubnormal_of_isNilpotent_finite H
      -- ⟨H, H^x⟩ ≤ M (M は H を含む唯一の極大).
      obtain ⟨K, hKcoatom, hKle⟩ :=
        (eq_top_or_exists_le_coatom (H ⊔ ((MulAut.conj x) • H : Subgroup G) :
          Subgroup G)).resolve_left hsup_ne_top
      have hHK : H ≤ K := le_sup_left.trans hKle
      have hKM : K = M := hMuniq K hKcoatom hHK
      exact (le_sup_right.trans hKle).trans hKM.le
    -- 正規閉包 `H^G ≤ M`.
    have hNH_le_M : Subgroup.normalClosure (H : Set G) ≤ M := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro y hy
      rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨a, haH, hConj⟩
      rcases hConj with ⟨c, hc⟩
      apply hHx_le_M (c : G)
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def]
      change ((c : G)⁻¹) * y * ((c : G)⁻¹)⁻¹ ∈ H
      rw [inv_inv]
      have hc_eq : (c : G) * a = y * (c : G) := hc
      have ha_eq : ((c : G)⁻¹) * y * ((c : G)) = a := by
        rw [mul_assoc, ← hc_eq]
        group
      rw [ha_eq]
      exact haH
    -- 正規閉包 < ⊤ (since ≤ M coatom).
    have hNH_lt : Subgroup.normalClosure (H : Set G) ≠ ⊤ := fun hNHtop =>
      hMcoatom.1 (le_top.antisymm (hNHtop.symm.le.trans hNH_le_M))
    -- IH を `normalClosure H` に適用.
    have hHle_NH : H ≤ Subgroup.normalClosure (H : Set G) :=
      Subgroup.le_normalClosure
    have hH_sn_in_NH : (H.subgroupOf (Subgroup.normalClosure (H : Set G))).IsSubnormal :=
      hIH _ hHle_NH hNH_lt
    have hNH_sn : (Subgroup.normalClosure (H : Set G)).IsSubnormal :=
      Subgroup.Normal.isSubnormal inferInstance
    exact hSnneg (Subgroup.IsSubnormal.trans hHle_NH hH_sn_in_NH hNH_sn)

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** 逆方向: `∀ x ∈ G, ⟨H, H^x⟩` 冪零 ⇒ `H ≤ F(G)`.

Isaacs p.55 の証明: Wielandt's Zipper Lemma (Thm 2.9) + Thm 2.2 経由の `|G|`-induction.
詳細は補助 [`le_fitting_of_baer_aux`](#le_fitting_of_baer_aux) の docstring 参照. -/
theorem le_fitting_of_baer_sup_conj_isNilpotent [Finite G] {H : Subgroup G}
    (hN : ∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G))) :
    H ≤ fitting G :=
  le_fitting_of_baer_aux (Nat.card G) G le_rfl hN

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** 完全形 (iff): 有限群 `G` の部分群 `H` について,
`H ≤ F(G) ↔ ∀ x ∈ G, ⟨H, H^x⟩ 冪零`.

順方向 (`baer_sup_conj_isNilpotent_of_le_fitting`) は F(G) ⊴ G の単なる帰結.
逆方向 (`le_fitting_of_baer_sup_conj_isNilpotent`) は Zipper Lemma 経由の核心. -/
theorem le_fitting_iff_baer_sup_conj_isNilpotent [Finite G] (H : Subgroup G) :
    H ≤ fitting G ↔
      ∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G)) :=
  ⟨fun hH => baer_sup_conj_isNilpotent_of_le_fitting hH,
   le_fitting_of_baer_sup_conj_isNilpotent⟩

/-! ### Lemma 2.14 (dihedral structure) + Thm 2.13 (Matsuyama)

Lemma 2.14 の full statement (D が dihedral group `DihedralGroup n` と同型) は別途.
ここでは Matsuyama 2.13 の証明に必要な核心のみ:
- `inv_by_two_involutions`: `t * z * t = z⁻¹` for `z ∈ ⟨s * t⟩` (Lemma 2.14 inversion).
- `mem_zpowers_or_mul_t_mem_of_mem_closure_pair`: ⟨{s, t}⟩ の元の構造 ∈ ⟨s*t⟩ または `x*t`.

これらから, `⟨{s, t}⟩` の non-2-power 位数の元は ⟨s*t⟩ にあると示し, Matsuyama に使う.
-/

/-- **Isaacs Lemma 2.14 essence (inversion)**: 2 つの involution `s, t ∈ G` の積 `s * t`
の zpower 部分群 `⟨s * t⟩` の任意の元は involution `t` で反転される.

書籍 p.56-57 Lemma 2.14(a),(b) の核心. Dihedral group の "rotation subgroup is inverted
by reflections" の代数版. Matsuyama 2.13 で奇素数位数元の存在から最終結論 `x^t = x⁻¹`
を導くのに使用. -/
theorem inv_by_two_involutions {s t : G} (hs : s * s = 1) (ht : t * t = 1) {z : G}
    (hz : z ∈ Subgroup.zpowers (s * t)) : t * z * t = z⁻¹ := by
  have ht_inv : t⁻¹ = t := (eq_inv_iff_mul_eq_one.mpr ht).symm
  have hs_inv : s⁻¹ = s := (eq_inv_iff_mul_eq_one.mpr hs).symm
  -- t * (s * t) * t⁻¹ = (s * t)⁻¹.
  have h_conj_st : t * (s * t) * t⁻¹ = (s * t)⁻¹ := by
    have h1 : t * (s * t) * t⁻¹ = t * s := by group
    rw [h1, mul_inv_rev, hs_inv, ht_inv]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
  calc t * z * t
      = t * (s * t) ^ n * t := by rw [← hn]
    _ = t * (s * t) ^ n * t⁻¹ := by congr 1; exact ht_inv.symm
    _ = (t * (s * t) * t⁻¹) ^ n := conj_zpow.symm
    _ = ((s * t)⁻¹) ^ n := by rw [h_conj_st]
    _ = ((s * t) ^ n)⁻¹ := inv_zpow _ _
    _ = z⁻¹ := by rw [hn]

/-- **Lemma 2.14 (structural form)**: 2 つの involution `s, t ∈ G` について,
`⟨{s, t}⟩` の任意の元は `⟨s * t⟩` に属するか, `x * t` (`x ∈ ⟨s * t⟩`) の形.

書籍 p.56-57 Lemma 2.14 の dihedral 構造の代数版. Closure induction で証明.
4 つの mul cases + 2 つの inv cases を `inv_by_two_involutions` で繋ぐ.

Matsuyama 2.13 で ⟨{s, t}⟩ が 2-group iff ⟨s*t⟩ が 2-group, を導くのに使用. -/
theorem mem_zpowers_or_mul_t_mem_of_mem_closure_pair {s t : G}
    (hs : s * s = 1) (ht : t * t = 1) {y : G}
    (hy : y ∈ Subgroup.closure ({s, t} : Set G)) :
    y ∈ Subgroup.zpowers (s * t) ∨ ∃ x ∈ Subgroup.zpowers (s * t), y = x * t := by
  have ht_inv : t⁻¹ = t := (eq_inv_iff_mul_eq_one.mpr ht).symm
  -- t * x = x⁻¹ * t for x ∈ ⟨s * t⟩.
  have h_t_mul : ∀ x ∈ Subgroup.zpowers (s * t), t * x = x⁻¹ * t := by
    intro x hx
    have h := inv_by_two_involutions hs ht hx
    have h' : t * x = x⁻¹ * t⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact h
    rwa [ht_inv] at h'
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy_eq | hy_mem
    · -- y = s.
      rw [hy_eq]
      right
      refine ⟨s * t, Subgroup.mem_zpowers _, ?_⟩
      rw [mul_assoc, ht, mul_one]
    · -- y ∈ {t}, i.e., y = t.
      rw [Set.mem_singleton_iff.mp hy_mem]
      right
      exact ⟨1, Subgroup.one_mem _, (one_mul t).symm⟩
  | one => left; exact Subgroup.one_mem _
  | mul a b _ _ iha ihb =>
    rcases iha with ha_K | ⟨a', ha'_K, ha_eq⟩
    · rcases ihb with hb_K | ⟨b', hb'_K, hb_eq⟩
      · left; exact Subgroup.mul_mem _ ha_K hb_K
      · subst hb_eq
        right
        refine ⟨a * b', Subgroup.mul_mem _ ha_K hb'_K, ?_⟩
        rw [← mul_assoc]
    · subst ha_eq
      rcases ihb with hb_K | ⟨b', hb'_K, hb_eq⟩
      · -- (a' * t) * b. Push t through: t * b = b⁻¹ * t.
        right
        refine ⟨a' * b⁻¹, Subgroup.mul_mem _ ha'_K (Subgroup.inv_mem _ hb_K), ?_⟩
        calc a' * t * b
            = a' * (t * b) := mul_assoc a' t b
          _ = a' * (b⁻¹ * t) := by rw [h_t_mul b hb_K]
          _ = (a' * b⁻¹) * t := (mul_assoc _ _ _).symm
      · subst hb_eq
        -- (a' * t) * (b' * t) = a' * b'⁻¹ ∈ K (using t² = 1 + inversion).
        left
        have h_eq : a' * t * (b' * t) = a' * b'⁻¹ := by
          calc a' * t * (b' * t)
              = a' * (t * b') * t := by group
            _ = a' * (b'⁻¹ * t) * t := by rw [h_t_mul b' hb'_K]
            _ = a' * b'⁻¹ * (t * t) := by group
            _ = a' * b'⁻¹ * 1 := by rw [ht]
            _ = a' * b'⁻¹ := mul_one _
        rw [h_eq]
        exact Subgroup.mul_mem _ ha'_K (Subgroup.inv_mem _ hb'_K)
  | inv y _ ihy =>
    rcases ihy with hy_K | ⟨y', hy'_K, hy_eq⟩
    · left; exact Subgroup.inv_mem _ hy_K
    · subst hy_eq
      -- y⁻¹ = (y' * t)⁻¹ = t⁻¹ * y'⁻¹ = t * y'⁻¹ = y' * t (using inversion: t * y'⁻¹ = y' * t).
      right
      refine ⟨y', hy'_K, ?_⟩
      calc (y' * t)⁻¹
          = t⁻¹ * y'⁻¹ := mul_inv_rev _ _
        _ = t * y'⁻¹ := by rw [ht_inv]
        _ = (y'⁻¹)⁻¹ * t := h_t_mul y'⁻¹ (Subgroup.inv_mem _ hy'_K)
        _ = y' * t := by rw [inv_inv]

/-! ### Helpers for Thm 2.13 (Matsuyama) -/

/-- 自然数の補助: `N > 0` で `N` が `2` のべきでないなら, 奇素数の約数が存在する. -/
private theorem exists_odd_prime_dvd_of_not_pow_two :
    ∀ N : ℕ, 0 < N → (∀ k : ℕ, N ≠ 2^k) → ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ Odd q := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro _ hN_not_pow
    have hN_ne_one : N ≠ 1 := fun h => hN_not_pow 0 (by rw [h, pow_zero])
    obtain ⟨q, hq, hq_dvd⟩ := Nat.exists_prime_and_dvd hN_ne_one
    by_cases hq_two : q = 2
    · subst hq_two
      obtain ⟨m, hm⟩ := hq_dvd
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hm; omega
        · exact h
      have hm_lt : m < N := by rw [hm]; omega
      have hm_not_pow : ∀ k, m ≠ 2^k := fun k hk => by
        apply hN_not_pow (k + 1)
        rw [hm, hk, pow_succ, mul_comm]
      obtain ⟨q', hq', hq'_dvd, hq'_odd⟩ := ih m hm_lt hm_pos hm_not_pow
      exact ⟨q', hq', dvd_trans hq'_dvd ⟨2, by rw [hm, Nat.mul_comm]⟩, hq'_odd⟩
    · exact ⟨q, hq, hq_dvd, hq.odd_of_ne_two hq_two⟩

/-- `H ≤ F(G)` で `H` が `p`-subgroup なら `H ≤ O_p(G)`.

証明: `F(G)` は冪零 ⇒ 各素数 `p` について Sylow `p` が一意 (`Sylow.normal_of_isNilpotent`
+ `Sylow.characteristic_of_normal`). `H` をその unique Sylow に含め, characteristic
in normal で `G` の正規 `p`-部分群 ⇒ `normal_pgroup_le_opCore` で `O_p(G)` 配下.

Matsuyama (Thm 2.13) と Baer-Suzuki p-core 単一元版 (`baerSuzuki_pCore`, lean-eval
problem) の両方で `F(G) → O_p(G)` 橋渡しに使う. -/
theorem mem_opCore_of_le_fitting_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hH_pgroup : IsPGroup p H) (hH_fit : H ≤ fitting G) :
    H ≤ opCore p G := by
  -- Lift H to a subgroup of fitting G.
  set Hin : Subgroup (fitting G) := H.subgroupOf (fitting G) with hHin_def
  have hHin_pgroup : IsPGroup p Hin :=
    hH_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hH_fit).symm
  -- Sylow p of fitting G containing Hin.
  obtain ⟨Q, hHin_le_Q⟩ := hHin_pgroup.exists_le_sylow
  haveI hQ_normal : (Q : Subgroup (fitting G)).Normal := Sylow.normal_of_isNilpotent _
  haveI hQ_char : (Q : Subgroup (fitting G)).Characteristic :=
    Sylow.characteristic_of_normal _ hQ_normal
  haveI : ((Q : Subgroup (fitting G)).map (fitting G).subtype).Normal := inferInstance
  have hpgroupG : IsPGroup p ((Q : Subgroup (fitting G)).map (fitting G).subtype) :=
    Q.2.map (fitting G).subtype
  have hQ_le_op : (Q : Subgroup (fitting G)).map (fitting G).subtype ≤ opCore p G :=
    normal_pgroup_le_opCore hpgroupG
  intro x hx
  have hx_fit : x ∈ fitting G := hH_fit hx
  have hx_Hin : (⟨x, hx_fit⟩ : fitting G) ∈ Hin := by
    rw [hHin_def, Subgroup.mem_subgroupOf]
    exact hx
  have hx_Q : (⟨x, hx_fit⟩ : fitting G) ∈ (Q : Subgroup (fitting G)) :=
    hHin_le_Q hx_Hin
  exact hQ_le_op ⟨⟨x, hx_fit⟩, hx_Q, rfl⟩

open scoped Pointwise in
/-- **Isaacs Thm 2.13 (Matsuyama)**: 有限群 `G` の involution `t` (`t * t = 1`) で
`t ∉ O_2(G)` ならば, 奇素数位数の元 `x` で `t * x * t = x⁻¹` (Isaacs notation `x^t = x⁻¹`).

書籍 p.57 の証明 (Goldschmidt の Burnside `p^a q^b` 定理 (両素数奇) を偶数位数に拡張する
Matsuyama の核心):
1. `T = ⟨t⟩` は 2-subgroup, `t ≠ 1`.
2. `t ∉ O_2(G)` ⇒ `T ⊄ F(G)` (補助 `mem_opCore_of_le_fitting_of_isPGroup`).
3. Baer 逆 (Thm 2.12 iff) で ∃ g, `⟨T, T^g⟩` 非冪零.
4. `s = g·t·g⁻¹` も involution. `s = t` なら `⟨T, T^g⟩ = T` で冪零, 矛盾.
5. `s ≠ t` で `⟨{s, t}⟩` 非冪零 ⇒ 非 2-group (有限 p-group は冪零).
6. ∃ 奇素数 `q ∣ |⟨{s, t}⟩|`. Cauchy で `y ∈ ⟨{s, t}⟩` で `orderOf y = q`.
7. 構造補題 (`mem_zpowers_or_mul_t_mem_of_mem_closure_pair`) で `y ∈ ⟨s*t⟩` or `y = x*t`.
   後者なら `y² = 1` で `q ∣ 2` 矛盾 (q odd).
8. `y ∈ ⟨s*t⟩` で Lemma 2.14 essence (`inv_by_two_involutions`) ⇒ `t * y * t = y⁻¹`. -/
theorem matsuyama [Finite G] {t : G} (ht_sq : t * t = 1)
    (ht_notin : t ∉ opCore 2 G) :
    ∃ x : G, ∃ p : ℕ, p.Prime ∧ Odd p ∧ orderOf x = p ∧ t * x * t = x⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Step 1: t ≠ 1.
  have ht_ne_one : t ≠ 1 := fun h => ht_notin (h ▸ Subgroup.one_mem _)
  set T : Subgroup G := Subgroup.zpowers t with hT_def
  -- orderOf t = 2.
  have h_ord_t : orderOf t = 2 := by
    have h_dvd : orderOf t ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht_sq)
    rcases (Nat.dvd_prime Nat.prime_two).mp h_dvd with hone | htwo
    · exact absurd (orderOf_eq_one_iff.mp hone) ht_ne_one
    · exact htwo
  have hT_pgroup : IsPGroup 2 T := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, h_ord_t, pow_one]
  -- Step 2: T ⊄ fitting G.
  have hT_not_fit : ¬ T ≤ fitting G := fun hTF => ht_notin
    (mem_opCore_of_le_fitting_of_isPGroup hT_pgroup hTF (Subgroup.mem_zpowers _))
  -- Step 3: Baer iff ⇒ ∃ g, ⟨T, T^g⟩ not nilpotent.
  have hExist : ∃ g : G, ¬ Group.IsNilpotent ↥(T ⊔ ((MulAut.conj g) • T : Subgroup G)) := by
    by_contra h
    push Not at h
    exact hT_not_fit ((le_fitting_iff_baer_sup_conj_isNilpotent T).mpr h)
  obtain ⟨g, hg⟩ := hExist
  -- Step 4: s := g·t·g⁻¹.
  set s : G := g * t * g⁻¹ with hs_def
  have hs_sq : s * s = 1 := by
    change (g * t * g⁻¹) * (g * t * g⁻¹) = 1
    calc (g * t * g⁻¹) * (g * t * g⁻¹)
        = g * t * (g⁻¹ * g) * t * g⁻¹ := by group
      _ = g * t * 1 * t * g⁻¹ := by rw [inv_mul_cancel]
      _ = g * (t * t) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [ht_sq]
      _ = 1 := by group
  -- T^g = zpowers s.
  have hTg_eq : ((MulAut.conj g) • T : Subgroup G) = Subgroup.zpowers s := by
    rw [hT_def, Subgroup.pointwise_smul_def]
    exact MonoidHom.map_zpowers _ _
  rw [hTg_eq] at hg
  -- Step 5: Case s = t ⇒ T ⊔ T = T nilpotent, 矛盾.
  by_cases hst : s = t
  · exfalso
    rw [hst, ← hT_def, sup_idem] at hg
    exact hg hT_pgroup.isNilpotent
  -- Step 6: s ≠ t. T ⊔ zpowers s = closure {s, t}.
  have h_sup_eq : T ⊔ Subgroup.zpowers s = Subgroup.closure ({s, t} : Set G) := by
    rw [hT_def, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        ← Subgroup.closure_union]
    congr 1
    ext x
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
  rw [h_sup_eq] at hg
  haveI hClosure_fin : Finite ↥(Subgroup.closure ({s, t} : Set G)) := Subtype.finite
  -- Step 7: ⟨{s, t}⟩ not 2-group.
  have h_not_pgroup : ¬ IsPGroup 2 ↥(Subgroup.closure ({s, t} : Set G)) := fun h =>
    hg h.isNilpotent
  have h_card_not_pow : ∀ k : ℕ,
      Nat.card ↥(Subgroup.closure ({s, t} : Set G)) ≠ 2^k := fun k hk =>
    h_not_pgroup (IsPGroup.iff_card.mpr ⟨k, hk⟩)
  obtain ⟨q, hq_prime, hq_dvd, hq_odd⟩ :=
    exists_odd_prime_dvd_of_not_pow_two _ Nat.card_pos h_card_not_pow
  haveI hq_fact : Fact q.Prime := ⟨hq_prime⟩
  -- Step 8: Cauchy ⇒ ∃ y of order q.
  obtain ⟨y, hy_ord⟩ := exists_prime_orderOf_dvd_card' q hq_dvd
  have h_ord_y_G : orderOf (y : G) = q := by
    rw [← hy_ord]; exact Subgroup.orderOf_coe y
  have hy_inG : (y : G) ∈ Subgroup.closure ({s, t} : Set G) := y.2
  -- Step 9: 構造補題で y ∈ ⟨s*t⟩ or y = x*t.
  rcases mem_zpowers_or_mul_t_mem_of_mem_closure_pair hs_sq ht_sq hy_inG with
    hy_K | ⟨x, hx_K, hy_eq⟩
  · -- y ∈ ⟨s*t⟩ ⇒ Lemma 2.14 で t * y * t = y⁻¹.
    exact ⟨(y : G), q, hq_prime, hq_odd, h_ord_y_G,
           inv_by_two_involutions hs_sq ht_sq hy_K⟩
  · -- y = x * t ⇒ y² = 1 ⇒ q ∣ 2 ⇒ q = 2, 矛盾 (q odd).
    exfalso
    have h_sq : (y : G) * (y : G) = 1 := by
      rw [hy_eq]
      calc (x * t) * (x * t)
          = x * (t * x * t) := by group
        _ = x * x⁻¹ := by rw [inv_by_two_involutions hs_sq ht_sq hx_K]
        _ = 1 := mul_inv_cancel x
    have h_ord_dvd : orderOf (y : G) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h_sq)
    rw [h_ord_y_G] at h_ord_dvd
    rcases (Nat.dvd_prime Nat.prime_two).mp h_ord_dvd with h1 | h2
    · exact hq_prime.one_lt.ne' h1
    · rw [h2] at hq_odd
      rcases hq_odd with ⟨k, hk⟩
      omega

/-! ### Baer-Suzuki theorem (single-element p-core form) -/

open scoped Pointwise in
/-- **Baer-Suzuki Theorem (single-element p-core form)**: 有限群 `G` の元 `x`,
素数 `p` について,
`x ∈ O_p(G) ↔ ∀ g : G, ⟨x, g·x·g⁻¹⟩` is a `p`-group.

これは Isaacs Thm 2.12 (Baer, `H ≤ F(G) ↔ ∀ x ∈ G, ⟨H, H^x⟩` 冪零) の
`H := ⟨x⟩` への特殊化と, `p`-元 ∈ `F(G)` ⇒ `p`-元 ∈ `O_p(G)`
([`mem_opCore_of_le_fitting_of_isPGroup`](#mem_opCore_of_le_fitting_of_isPGroup))
の合成で得られる.

- 順方向 (`⇒`): `O_p(G) ⊴ G` で共役不変 ⇒ `closure {x, gxg⁻¹} ≤ O_p(G)`,
  `O_p(G)` は `p`-群 ⇒ 部分群も `p`-群.
- 逆方向 (`⇐`): `g = 1` で `⟨x⟩` が `p`-群; 各 `g` で `⟨x⟩ ⊔ ⟨x⟩^g
  = ⟨x, gxg⁻¹⟩` が `p`-群 ⇒ 冪零. Baer 2.12 で `⟨x⟩ ≤ F(G)`, 橋渡し
  で `⟨x⟩ ≤ O_p(G)`.

lean-eval problem suite signature:
<https://lean-lang.org/eval/problems/baer_suzuki/>
(eval 側の `LeanEval.GroupTheory.Defs.pCore` は本 repo の
[`OddOrder.Isaacs.Ch01.opCore`](Ch01_Sylow/Main.lean#L533) と同じく最大正規 `p`-部分群).

古典 Baer-Suzuki theorem は通常 subset 版 (`X ⊆ O_p(G) ↔ ∀ a b ∈ X,
⟨a, b⟩` p-群) で語られるが, 本定理はその単一元への特殊化. -/
theorem baerSuzuki_pCore [Finite G] {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ opCore p G ↔
      ∀ g : G, IsPGroup p ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
  refine ⟨?_, ?_⟩
  · -- (⇒) x ∈ O_p(G) ⇒ closure {x, gxg⁻¹} ≤ O_p(G), 部分群は p-群.
    intro hx g
    have hOp_pgroup : IsPGroup p ↥(opCore p G) := opCore_isPGroup p G
    have hgx : g * x * g⁻¹ ∈ opCore p G :=
      (opCore.normal p G).conj_mem x hx g
    have hclos_le : Subgroup.closure ({x, g * x * g⁻¹} : Set G) ≤ opCore p G := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | hy
      · exact hx
      · rw [Set.mem_singleton_iff] at hy
        exact hy ▸ hgx
    exact hOp_pgroup.of_injective (Subgroup.inclusion hclos_le)
      (Subgroup.inclusion_injective hclos_le)
  · -- (⇐) ∀ g, closure {x, gxg⁻¹} p-群 ⇒ Isaacs 2.12 iff で ⟨x⟩ ≤ F(G), 橋渡しで x ∈ O_p(G).
    intro hPg
    -- ⟨x⟩ は p-群 (g = 1 で closure {x, x} = ⟨x⟩).
    have hx_pgroup : IsPGroup p ↥(Subgroup.zpowers x) := by
      have h1 := hPg 1
      have h_set : ({x, 1 * x * 1⁻¹} : Set G) = {x} := by simp
      rw [h_set, ← Subgroup.zpowers_eq_closure] at h1
      exact h1
    -- ⟨x⟩ ⊔ (MulAut.conj g) • ⟨x⟩ = closure {x, gxg⁻¹}.
    have hsup_eq : ∀ g : G,
        (Subgroup.zpowers x ⊔ ((MulAut.conj g) • Subgroup.zpowers x : Subgroup G))
          = Subgroup.closure ({x, g * x * g⁻¹} : Set G) := by
      intro g
      -- まず (MulAut.conj g) • ⟨x⟩ = ⟨gxg⁻¹⟩.
      have h_conj : (MulAut.conj g : MulAut G) • Subgroup.zpowers x
          = Subgroup.zpowers (g * x * g⁻¹) := by
        rw [Subgroup.zpowers_eq_closure x,
            Subgroup.zpowers_eq_closure (g * x * g⁻¹),
            Subgroup.smul_closure]
        congr 1
        ext y
        simp [MulAut.smul_def, MulAut.conj_apply]
      -- closure {x} ⊔ closure {gxg⁻¹} = closure ({x} ∪ {gxg⁻¹}) = closure {x, gxg⁻¹}.
      rw [h_conj, Subgroup.zpowers_eq_closure x,
          Subgroup.zpowers_eq_closure (g * x * g⁻¹),
          ← Subgroup.closure_union]
      congr 1
    -- Baer 仮定: ∀ g, ⟨x⟩ ⊔ ⟨x⟩^g 冪零.
    have hbaer : ∀ g : G,
        Group.IsNilpotent ↥(Subgroup.zpowers x ⊔
          ((MulAut.conj g) • Subgroup.zpowers x : Subgroup G)) := by
      intro g
      rw [hsup_eq g]
      exact (hPg g).isNilpotent
    -- Isaacs 2.12 iff ⇒ ⟨x⟩ ≤ F(G).
    have hxle_fit : Subgroup.zpowers x ≤ fitting G :=
      (le_fitting_iff_baer_sup_conj_isNilpotent _).mpr hbaer
    -- 橋渡し: ⟨x⟩ p-群 + ⟨x⟩ ≤ F(G) ⇒ ⟨x⟩ ≤ O_p(G).
    exact mem_opCore_of_le_fitting_of_isPGroup hx_pgroup hxle_fit
      (Subgroup.mem_zpowers x)

end -- 2B

section /- 2C: p-local subgroups (pp. 58-61) -/

variable {G : Type*} [Group G]

/-- **p-local 部分群**: 非自明 p-部分群 `P ≤ G` の正規化群 `N_G(P)` として表せる部分群.

Isaacs p.58 定義: "A subgroup `H` of a group `G` is `p`**-local**, where `p` is prime,
if `H` is of the form `H = N_G(P)`, where `P` is some nonidentity `p`-subgroup of `G`." -/
def IsPLocal (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ P : Subgroup G, P ≠ ⊥ ∧ IsPGroup p P ∧ H = Subgroup.normalizer (P : Set G)

/-- **local 部分群**: ある素数 `p` について `p`-local. -/
def IsLocal (H : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ IsPLocal p H

set_option maxHeartbeats 1200000 in
-- 長い構成的証明 (Sylow II + Frattini, ↥M 内で構築 + G への持ち上げ) のため heartbeat を増やす.
/-- **Isaacs Lemma 2.16** (lifting p-local subgroups from a quotient).

Let `N ⊴ G` and `Ḡ = G/N`. For every prime `p`, every `p`-local subgroup `Mbar` of `Ḡ`
has the form `L̄` where `L` is a `p`-local subgroup of `G`.

書籍 p.59 の証明:
1. `Mbar = N_Ḡ(Ubar)` で `Ubar` は非自明 `p`-部分群.
2. 対応定理で `Ubar = U/N`, `N < U ≤ G`. `M := Mbar.comap (mk' N) = N_G(U)`
   (`comap_normalizer_eq_of_surjective`).
3. `P ∈ Syl_p(U)` を取り `P_G := P.map U.subtype ≤ U ≤ G`. `Ubar` 非自明 ⇒ `p ∣ |Ubar| ∣ |U|`
   ⇒ `P_G ≠ ⊥`.
4. `U = N · P_G`: `|U:N| = |Ubar|` は p-冪, `|U:P_G|` は p と互いに素 ⇒ gcd = 1.
5. `L := N_G(P_G)`. `P_G` 非自明 p-群 ⇒ `L` は p-local.
6. `L ⊆ M`: `L` は `N` (`N ⊴ G`) と `P_G` を正規化 ⇒ `N ⊔ P_G = U` を正規化 ⇒ `L ⊆ N_G(U) = M`.
7. `M ⊆ N · L` (Frattini in ↥M): `U.subgroupOf M ⊴ ↥M` (M = N_G(U)). `P` を `↥(U.subgroupOf M)`
   の Sylow と同一視し `Sylow.normalizer_sup_eq_top` で `N_↥M(P) ⊔ U.subgroupOf M = ⊤_↥M`.
   ↥M から G へ持ち上げ `M ⊆ U · L = (N · P_G) · L = N · L`.
8. 商に送る: `M.map f = (N ⊔ L).map f = N.map f ⊔ L.map f = ⊥ ⊔ L.map f = L.map f = Mbar`. -/
theorem isPLocal_of_quotient [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    {Mbar : Subgroup (G ⧸ N)} (hMbar : IsPLocal p Mbar) :
    ∃ L : Subgroup G, IsPLocal p L ∧ L.map (QuotientGroup.mk' N) = Mbar := by
  classical
  -- Step 1: unpack Mbar = N_Ḡ(Ubar).
  obtain ⟨Ubar, hUbar_ne, hUbar_pgroup, hMbar_eq⟩ := hMbar
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective N
  have hf_ker : f.ker = N := QuotientGroup.ker_mk' N
  -- Step 2: U := comap f Ubar, M := comap f Mbar = normalizer U.
  set U : Subgroup G := Ubar.comap f with hU_def
  set M : Subgroup G := Mbar.comap f with hM_def
  have hN_le_U : N ≤ U := by
    intro x hx
    have hfx : f x = 1 := by
      have : x ∈ f.ker := by rw [hf_ker]; exact hx
      exact this
    rw [hU_def, Subgroup.mem_comap, hfx]
    exact Subgroup.one_mem _
  have hU_map : U.map f = Ubar := by
    rw [hU_def]; exact Subgroup.map_comap_eq_self_of_surjective hf_surj Ubar
  have hM_map : M.map f = Mbar := by
    rw [hM_def]; exact Subgroup.map_comap_eq_self_of_surjective hf_surj Mbar
  have hM_eq_norm : M = Subgroup.normalizer U := by
    rw [hM_def, hMbar_eq]
    exact Subgroup.comap_normalizer_eq_of_surjective Ubar hf_surj
  -- U ≤ M.
  have hU_le_M : U ≤ M := by rw [hM_eq_norm]; exact Subgroup.le_normalizer
  -- Step 3: pick a Sylow p-subgroup of U and lift to G.
  haveI : Finite ↥U := Subtype.finite
  let P : Sylow p ↥U := default
  set P_G : Subgroup G := (P : Subgroup ↥U).map U.subtype with hPG_def
  have hP_pgroup : IsPGroup p ↥P_G := P.2.map U.subtype
  have hP_le_U : P_G ≤ U := by
    rw [hPG_def]
    intro y hy; obtain ⟨z, _, hz⟩ := hy; rw [← hz]; exact z.2
  -- |Ubar| > 1 since Ubar ≠ ⊥, and Ubar p-group, so p ∣ |Ubar|.
  obtain ⟨k, hUbar_card⟩ : ∃ k, Nat.card ↥Ubar = p ^ k := IsPGroup.iff_card.mp hUbar_pgroup
  have hUbar_card_pos : 1 < Nat.card ↥Ubar := by
    have h_ne_one : Nat.card ↥Ubar ≠ 1 := by
      intro h
      apply hUbar_ne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have h_sub : Subsingleton ↥Ubar := (Nat.card_eq_one_iff_unique.mp h).1
      have : (⟨x, hx⟩ : ↥Ubar) = ⟨1, Subgroup.one_mem _⟩ := Subsingleton.elim _ _
      exact Subtype.ext_iff.mp this
    have h_pos : 0 < Nat.card ↥Ubar := Nat.card_pos
    omega
  have hk_pos : 0 < k := by
    by_contra h
    push Not at h
    interval_cases k
    rw [pow_zero] at hUbar_card
    omega
  have hp_dvd_Ubar : p ∣ Nat.card ↥Ubar := by
    rw [hUbar_card]; exact dvd_pow_self p hk_pos.ne'
  -- |U/N.subgroupOf U| = |Ubar|.
  have hU_quot_card : Nat.card (↥U ⧸ N.subgroupOf U) = Nat.card ↥Ubar := by
    rw [← hU_map]
    let g : ↥U →* G ⧸ N := f.comp U.subtype
    have hg_range : g.range = U.map f := by
      simp [g, MonoidHom.range_comp, Subgroup.range_subtype]
    have hg_ker : g.ker = N.subgroupOf U := by
      ext x
      constructor
      · intro hx
        have : f (x : G) = 1 := hx
        have hxN : (x : G) ∈ N := by rw [← hf_ker]; exact this
        exact hxN
      · intro hx
        have hxN : (x : G) ∈ N := hx
        have : (x : G) ∈ f.ker := by rw [hf_ker]; exact hxN
        exact this
    have h_iso : (↥U) ⧸ g.ker ≃* ↥g.range :=
      QuotientGroup.quotientKerEquivRange g
    have h_card_eq : Nat.card ((↥U) ⧸ g.ker) = Nat.card ↥g.range :=
      Nat.card_congr h_iso.toEquiv
    rw [hg_ker] at h_card_eq
    rw [h_card_eq, hg_range]
  have hN_subU_index : (N.subgroupOf U).index = Nat.card ↥Ubar := by
    rw [Subgroup.index_eq_card]; exact hU_quot_card
  have hp_dvd_U : p ∣ Nat.card ↥U := by
    have h_idx_dvd : (N.subgroupOf U).index ∣ Nat.card ↥U := Subgroup.index_dvd_card _
    rw [hN_subU_index] at h_idx_dvd
    exact dvd_trans hp_dvd_Ubar h_idx_dvd
  have hp_dvd_P : p ∣ Nat.card ↥(P : Subgroup ↥U) :=
    P.dvd_card_of_dvd_card hp_dvd_U
  have hP_ne_bot_inU : (P : Subgroup ↥U) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hp_dvd_P
    exact (Fact.out : p.Prime).not_dvd_one hp_dvd_P
  have hPG_ne_bot : P_G ≠ ⊥ := by
    intro hbot
    apply hP_ne_bot_inU
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx_G : (x : G) ∈ P_G := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hx_G
    exact Subtype.ext hx_G
  -- Step 4: N ⊔ P_G = U.
  have hP_idx_not_dvd : ¬ p ∣ (P : Subgroup ↥U).index := P.not_dvd_index
  have hN_P_sup_top : N.subgroupOf U ⊔ (P : Subgroup ↥U) = ⊤ := by
    rw [← Subgroup.index_eq_one]
    have h_dvd_N : (N.subgroupOf U ⊔ (P : Subgroup ↥U)).index ∣ (N.subgroupOf U).index :=
      Subgroup.index_dvd_of_le le_sup_left
    have h_dvd_P : (N.subgroupOf U ⊔ (P : Subgroup ↥U)).index ∣ (P : Subgroup ↥U).index :=
      Subgroup.index_dvd_of_le le_sup_right
    rw [hN_subU_index, hUbar_card] at h_dvd_N
    have hp_prime : p.Prime := Fact.out
    have h_coprime : Nat.Coprime (p ^ k) (P : Subgroup ↥U).index :=
      Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hP_idx_not_dvd)
    exact Nat.eq_one_of_dvd_coprimes h_coprime h_dvd_N h_dvd_P
  have hN_PG_sup_U : N ⊔ P_G = U := by
    have h_sub_map : (N.subgroupOf U ⊔ (P : Subgroup ↥U)).map U.subtype = U := by
      rw [hN_P_sup_top, ← MonoidHom.range_eq_map, U.range_subtype]
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hN_le_U] at h_sub_map
    rw [← hPG_def] at h_sub_map
    exact h_sub_map
  -- Step 5: L = normalizer P_G is p-local.
  set L : Subgroup G := Subgroup.normalizer P_G with hL_def
  have hL_pLocal : IsPLocal p L := ⟨P_G, hPG_ne_bot, hP_pgroup, rfl⟩
  -- Step 6: L ⊆ M = N_G(U) = N_G(N ⊔ P_G).
  -- L normalizes N (N ⊴ G) and P_G (by def), hence N ⊔ P_G = U.
  -- Helper: if g normalizes both N and P_G then g normalizes N ⊔ P_G.
  have h_preserve : ∀ (g : G), (∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      (∀ q ∈ P_G, g * q * g⁻¹ ∈ P_G) →
      ∀ z ∈ N ⊔ P_G, g * z * g⁻¹ ∈ N ⊔ P_G := by
    intro g hgN hgPG z hz
    rw [Subgroup.sup_eq_closure] at hz
    induction hz using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with hwN | hwPG
      · exact Subgroup.mem_sup_left (hgN w hwN)
      · exact Subgroup.mem_sup_right (hgPG w hwPG)
    | one =>
      have h1 : g * 1 * g⁻¹ = 1 := by group
      rw [h1]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb =>
      have h_eq : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [h_eq]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have h_eq : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [h_eq]; exact Subgroup.inv_mem _ ha
  have hL_le_M : L ≤ M := by
    rw [hM_eq_norm]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    have h_conj_N : ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun n hn =>
      Subgroup.Normal.conj_mem ‹N.Normal› n hn x
    have h_conj_N_inv : ∀ n ∈ N, x⁻¹ * n * (x⁻¹)⁻¹ ∈ N := fun n hn =>
      Subgroup.Normal.conj_mem ‹N.Normal› n hn x⁻¹
    have hx_in_norm : x ∈ Subgroup.normalizer (P_G : Set G) := hx
    have hx_inv_in_norm : x⁻¹ ∈ Subgroup.normalizer (P_G : Set G) :=
      Subgroup.inv_mem _ hx
    have h_conj_PG : ∀ q ∈ P_G, x * q * x⁻¹ ∈ P_G :=
      fun q hq => (Subgroup.mem_normalizer_iff.mp hx_in_norm q).mp hq
    have h_conj_PG_inv : ∀ q ∈ P_G, x⁻¹ * q * (x⁻¹)⁻¹ ∈ P_G :=
      fun q hq => (Subgroup.mem_normalizer_iff.mp hx_inv_in_norm q).mp hq
    intro y
    constructor
    · intro hy
      rw [← hN_PG_sup_U] at hy ⊢
      exact h_preserve x h_conj_N h_conj_PG y hy
    · intro hy
      rw [← hN_PG_sup_U] at hy ⊢
      have h_pre : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ N ⊔ P_G :=
        h_preserve x⁻¹ h_conj_N_inv h_conj_PG_inv _ hy
      have h_simp : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
      rwa [h_simp] at h_pre
  -- Step 7: M ⊆ N ⊔ L (Frattini argument inside ↥M).
  -- We have U ⊴ M (M = normalizer U). View U.subgroupOf M as a normal subgroup of ↥M.
  -- Pick the Sylow corresponding to P inside ↥(U.subgroupOf M) (using ↥(U.subgroupOf M) ≃ ↥U).
  -- Apply Sylow.normalizer_sup_eq_top to get N_↥M(P_M.map _) ⊔ U.subgroupOf M = ⊤.
  have hM_le_N_sup_L : M ≤ N ⊔ L := by
    -- Set up the normality of U.subgroupOf M.
    haveI hUM_normal : (U.subgroupOf M).Normal := by
      rw [hM_eq_norm]
      exact Subgroup.normal_in_normalizer
    -- The isomorphism ↥(U.subgroupOf M) ≃* ↥U lifts the Sylow P.
    let e : ↥(U.subgroupOf M) ≃* ↥U := Subgroup.subgroupOfEquivOfLe hU_le_M
    -- Transport P : Sylow p ↥U back to a Sylow of ↥(U.subgroupOf M).
    let P_M : Sylow p ↥(U.subgroupOf M) :=
      Sylow.ofCard ((P : Subgroup ↥U).comap e.toMonoidHom) (by
        rw [show Nat.card ↥(U.subgroupOf M) = Nat.card ↥U from
          Nat.card_congr e.toEquiv]
        -- The preimage under e is in bijection with P.
        have h_card_eq : Nat.card ↥((P : Subgroup ↥U).comap e.toMonoidHom) =
            Nat.card (P : Subgroup ↥U) := by
          refine Nat.card_congr ?_
          exact {
            toFun := fun x => ⟨e x.1, x.2⟩
            invFun := fun y => ⟨e.symm y.1, by
              change e (e.symm y.1) ∈ (P : Subgroup ↥U)
              rw [MulEquiv.apply_symm_apply]
              exact y.2⟩
            left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
            right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
          }
        rw [h_card_eq, Sylow.card_eq_multiplicity P])
    -- Apply Sylow.normalizer_sup_eq_top in ↥M.
    haveI : Finite ↥M := Subtype.finite
    haveI : Finite ↥(U.subgroupOf M) := Subtype.finite
    have h_frattini : Subgroup.normalizer (P_M.map (U.subgroupOf M).subtype) ⊔
        U.subgroupOf M = ⊤ :=
      Sylow.normalizer_sup_eq_top P_M
    -- Identify P_M.map (U.subgroupOf M).subtype.map M.subtype = P_G.
    have h_PM_map_eq : ((P_M.map (U.subgroupOf M).subtype : Subgroup ↥M).map M.subtype) =
        P_G := by
      -- (P_M.map (U.subgroupOf M).subtype).map M.subtype as a set in G:
      -- elements are M.subtype (U.subgroupOf M).subtype z for z in P_M.
      ext y
      simp only [Subgroup.mem_map, Subgroup.coe_subtype, P_G]
      constructor
      · rintro ⟨a, ⟨b, hb, hba⟩, hay⟩
        -- b ∈ P_M, (U.subgroupOf M).subtype b = a, M.subtype a = y.
        -- P_M corresponds to (P : Subgroup ↥U).comap e via e iso.
        -- So b ∈ P_M iff e b ∈ P.
        have hb' : e b ∈ (P : Subgroup ↥U) := by
          change b ∈ (P : Subgroup ↥U).comap e.toMonoidHom at hb
          rw [Subgroup.mem_comap] at hb; exact hb
        refine ⟨e b, hb', ?_⟩
        -- Need: U.subtype (e b) = y.
        -- y = M.subtype a = a.val, a = (U.subgroupOf M).subtype b = b.val (as element of ↥M).
        -- (U.subgroupOf M).subtype b ∈ ↥M, so a.val = b.val.val. y = b.val.val.
        -- e b : ↥U has e b.val = b.val.val (by definition of subgroupOfEquivOfLe).
        have he_val : ((e b : ↥U) : G) = ((b : ↥(U.subgroupOf M)) : ↥M).1 := by
          rfl
        rw [← hay, ← hba]
        change ((b : ↥(U.subgroupOf M)) : ↥M).1 = _
        rw [← he_val]
      · rintro ⟨z, hzP, hzy⟩
        -- z ∈ P, U.subtype z = y. Lift z back through e to b : ↥(U.subgroupOf M).
        refine ⟨⟨z, hU_le_M z.2⟩, ⟨e.symm z, ?_, ?_⟩, ?_⟩
        · change e.symm z ∈ (P : Subgroup ↥U).comap e.toMonoidHom
          rw [Subgroup.mem_comap]
          simp only [MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom]
          exact hzP
        · -- (U.subgroupOf M).subtype (e.symm z) = ⟨z.val, hU_le_M z.2⟩
          rfl
        · exact hzy
    -- Now use Frattini: each m ∈ M lifts to ⟨m, hm⟩ : ↥M, decomposes as a * b
    -- with a ∈ normalizer(P_M.map (U.subgroupOf M).subtype), b ∈ U.subgroupOf M.
    -- Lifting: M.subtype a ∈ L (= normalizer P_G in G), M.subtype b ∈ U.
    intro m hm
    have hm_M : (⟨m, hm⟩ : ↥M) ∈ (⊤ : Subgroup ↥M) := trivial
    rw [← h_frattini] at hm_M
    -- Use the characterization of sup via `mem_sup_of_normal_right`.
    rcases Subgroup.mem_sup_of_normal_right.mp hm_M with ⟨a, ha, b, hb, hab⟩
    -- a ∈ normalizer (P_M.map ...), b ∈ U.subgroupOf M. a * b = ⟨m, hm⟩.
    -- M.subtype b ∈ U.
    have hMb_U : (b : G) ∈ U := by
      change b ∈ U.subgroupOf M at hb
      exact hb
    -- M.subtype a ∈ L = normalizer P_G in G.
    have hMa_L : (a : G) ∈ L := by
      rw [hL_def, Subgroup.mem_normalizer_iff]
      intro y
      -- a normalizes P_M.map (U.subgroupOf M).subtype in ↥M.
      have ha_norm : a ∈ Subgroup.normalizer (P_M.map (U.subgroupOf M).subtype) := ha
      rw [Subgroup.mem_normalizer_iff] at ha_norm
      constructor
      · intro hy
        -- y ∈ P_G; need a * y * a⁻¹ ∈ P_G.
        -- y ∈ P_G ⊆ U ⊆ M, so y ∈ ↥M. y as element of ↥M is in P_M.map (U.subgroupOf M).subtype.
        have hy_U : y ∈ U := hP_le_U hy
        have hy_M : y ∈ M := hU_le_M hy_U
        have hy_PM_map : (⟨y, hy_M⟩ : ↥M) ∈ P_M.map (U.subgroupOf M).subtype := by
          -- Equivalently y ∈ (P_M.map _).map M.subtype = P_G.
          rw [← h_PM_map_eq] at hy
          rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
          have hx_eq : x = ⟨y, hy_M⟩ := Subtype.ext hxy
          rw [hx_eq] at hx; exact hx
        have h_step := (ha_norm ⟨y, hy_M⟩).mp hy_PM_map
        -- h_step : a * ⟨y, hy_M⟩ * a⁻¹ ∈ P_M.map ...
        -- Lift to G via M.subtype.
        have h_step_G : (a : G) * y * (a : G)⁻¹ ∈ P_G := by
          rw [← h_PM_map_eq]
          refine ⟨a * ⟨y, hy_M⟩ * a⁻¹, h_step, ?_⟩
          rfl
        exact h_step_G
      · intro hy
        -- Need y ∈ P_G given a * y * a⁻¹ ∈ P_G.
        -- Use a⁻¹ ∈ normalizer (P_M.map ...).
        have ha_inv_norm : a⁻¹ ∈ Subgroup.normalizer (P_M.map (U.subgroupOf M).subtype) :=
          (Subgroup.normalizer _).inv_mem ha
        rw [Subgroup.mem_normalizer_iff] at ha_inv_norm
        -- We want y ∈ P_G. Have aya⁻¹ ∈ P_G ⊆ U ⊆ M.
        have hay_U : (a : G) * y * (a : G)⁻¹ ∈ U := hP_le_U hy
        -- We need y ∈ M to use the lift.
        -- a * y * a⁻¹ ∈ U ⊆ M, so a * y * a⁻¹ ∈ ↥M.
        -- y = a⁻¹ * (a y a⁻¹) * a ∈ M.
        have hy_M : y ∈ M := by
          have : (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * ((a : G)⁻¹)⁻¹ = y := by group
          rw [← this]
          exact M.mul_mem (M.mul_mem (M.inv_mem a.2) (hU_le_M hay_U)) (M.inv_mem (M.inv_mem a.2))
        have hay_PM_map : (⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩ : ↥M)
            ∈ P_M.map (U.subgroupOf M).subtype := by
          rw [← h_PM_map_eq] at hy
          rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
          have hx_eq : x = ⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩ := Subtype.ext hxy
          rw [hx_eq] at hx; exact hx
        -- a⁻¹ * (aya⁻¹) * a = y, and a⁻¹ * (aya⁻¹) * (a⁻¹)⁻¹ ∈ P_M.map ... by ha_inv_norm.
        have h_back := (ha_inv_norm ⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩).mp hay_PM_map
        have h_back_G : (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * ((a : G)⁻¹)⁻¹ ∈ P_G := by
          rw [← h_PM_map_eq]
          refine ⟨a⁻¹ * ⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩ * (a⁻¹)⁻¹, h_back, ?_⟩
          rfl
        have h_simp : (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * ((a : G)⁻¹)⁻¹ = y := by group
        rwa [h_simp] at h_back_G
    -- m = (M.subtype a) * (M.subtype b).
    have hm_eq : m = (a : G) * (b : G) := by
      have h := congrArg ((↑) : ↥M → G) hab
      simp at h; exact h.symm
    -- (M.subtype b) ∈ U = N ⊔ P_G, decompose.
    have hb_NL : (b : G) ∈ N ⊔ L := by
      rw [← hN_PG_sup_U] at hMb_U
      rcases Subgroup.mem_sup_of_normal_left.mp hMb_U with ⟨n, hn, q, hq, hq_eq⟩
      have hq_in_L : q ∈ L := by
        rw [hL_def]; exact Subgroup.le_normalizer hq
      rw [← hq_eq]
      exact (N ⊔ L).mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hq_in_L)
    have ha_NL : (a : G) ∈ N ⊔ L := Subgroup.mem_sup_right hMa_L
    rw [hm_eq]
    exact (N ⊔ L).mul_mem ha_NL hb_NL
  -- Step 8: send to quotient.
  refine ⟨L, hL_pLocal, ?_⟩
  apply le_antisymm
  · rw [← hM_map]
    exact Subgroup.map_mono hL_le_M
  · rw [← hM_map]
    have h_step1 : M.map f ≤ (N ⊔ L).map f := Subgroup.map_mono hM_le_N_sup_L
    have h_step2 : (N ⊔ L).map f = L.map f := by
      rw [Subgroup.map_sup]
      have h_N_map : N.map f = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        rcases hx with ⟨y, hy, hyx⟩
        rw [Subgroup.mem_bot]
        rw [← hyx]
        have : y ∈ f.ker := by rw [hf_ker]; exact hy
        exact this
      rw [h_N_map, bot_sup_eq]
    rw [← h_step2]
    exact h_step1

end
end OddOrder.Isaacs.Ch02
