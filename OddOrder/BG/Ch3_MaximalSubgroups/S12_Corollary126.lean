/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem125

/-!
# BG §12: Corollary 12.6 — `A ⊴ E` and centralizer control

**スコープ**: BG Chapter III §12, Corollary 12.6 (pp. 85-86, mmd L3179-3196)。
`p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)` のときの `E` 内での `A` の支配性。Theorem 12.5 の系。

## 主要結果 (部分ごとに standalone; 最終 assembly は `elemAb_normal_in_E_of_tau2`)

- `sup_Msigma_inf_E_eq_of_le`: Dedekind 等式 `(M_σ ⊔ A) ⊓ E = A`。
- `E_le_normalizer_of_tau2` (**12.6(a) 第1部**): `A ⊴ E` (Theorem 12.5(c) から)。
- `line_le_of_le_E_of_tau2` (**12.6(a) 第2部**): `ℰ_p¹(E) = ℰ¹(A)` — `E` の任意の line は
  `A` に入る (`Ω₁(P) = A` = `omega1_eq_of_tau2` 経由)。
- `centralizer_le_E_of_tau2` (**12.6(b)**): `C_G(A) ≤ E`, `N_M(A) = E`, `N_G(A) ⊄ M`。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Dedekind identity for the §12 setup**: `(M_σ ⊔ A) ⊓ E = A` for `A ≤ E`
(decompose in `↥M` along the normal `M_σ` and use `M_σ ⊓ E = 1`). -/
theorem sup_Msigma_inf_E_eq_of_le [Finite G]
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {A : Subgroup G} (hAE : A ≤ E) :
    (S10.Msigma M ⊔ A) ⊓ E = A := by
  refine le_antisymm ?_ (le_inf le_sup_right hAE)
  rintro x ⟨hxsup, hxE⟩
  have hMσM : S10.Msigma M ≤ M := S10.Msigma_le M
  have hAM : A ≤ M := hAE.trans h.E_le
  have hxM : x ∈ M := h.E_le hxE
  haveI : ((S10.Msigma M).subgroupOf M).Normal := by
    rw [S10.Msigma_subgroupOf]; infer_instance
  have hsub : (⟨x, hxM⟩ : ↥M) ∈ (S10.Msigma M).subgroupOf M ⊔ A.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup hMσM hAM]
    exact Subgroup.mem_subgroupOf.mpr hxsup
  have hsub' : (⟨x, hxM⟩ : ↥M) ∈
      ((S10.Msigma M).subgroupOf M : Set ↥M) * (A.subgroupOf M : Set ↥M) := by
    rw [← Subgroup.normal_mul]
    exact hsub
  obtain ⟨s, hs, a, ha, hsa⟩ := hsub'
  have hseq : (s : ↥M) = ⟨x, hxM⟩ * a⁻¹ := by rw [← hsa]; group
  have hsE : (s : G) ∈ E := by
    have hcoe : (s : G) = x * ((a : ↥M) : G)⁻¹ := by rw [hseq]; rfl
    rw [hcoe]
    exact E.mul_mem hxE (E.inv_mem (hAE (Subgroup.mem_subgroupOf.mp ha)))
  have hsbot : (s : G) ∈ S10.Msigma M ⊓ E := ⟨Subgroup.mem_subgroupOf.mp hs, hsE⟩
  rw [h.E_compl_inf, Subgroup.mem_bot] at hsbot
  have hxa : (⟨x, hxM⟩ : ↥M) = a := by
    rw [← hsa, show s = 1 from Subtype.ext hsbot]
    exact one_mul a
  have hxa' : x = ((a : ↥M) : G) := congrArg Subtype.val hxa
  rw [hxa']
  exact Subgroup.mem_subgroupOf.mp ha

/-- **BG Corollary 12.6(a), first part** (mmd L3192): `E ≤ N_G(A)` — from
`M_σ A ⊴ M` (Theorem 12.5(c)) and the Dedekind identity. -/
theorem E_le_normalizer_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau2 M) {A : Subgroup G}
    (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    E ≤ Subgroup.normalizer (A : Set G) := by
  have hAM : A ≤ M := hAE.trans h.E_le
  have h125c := (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.2.1
  have hinf := sup_Msigma_inf_E_eq_of_le h hAE
  have key : ∀ y ∈ E, ∀ g ∈ A, y * g * y⁻¹ ∈ A := by
    intro y hy g hg
    rw [← hinf]
    refine ⟨?_, E.mul_mem (E.mul_mem hy (hAE hg)) (E.inv_mem hy)⟩
    exact (Subgroup.mem_normalizer_iff.mp (h125c (h.E_le hy)) g).mp
      (Subgroup.mem_sup_right hg)
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => key e he x hx
  · intro hx
    have h1 := key e⁻¹ (E.inv_mem he) _ hx
    simpa [mul_assoc] using h1

/-- **BG Corollary 12.6(a), second part** (mmd L3192-3194): every line
`X ∈ ℰ_p¹(E)` lies in `A` (i.e. `ℰ_p¹(E) = ℰ¹(A)`): `X ⊔ A` is a `p`-subgroup of `M`,
hence lies in a Sylow `p`-subgroup `P ⊇ A`, and `Ω₁(P) = A` (`omega1_eq_of_tau2`)
absorbs the exponent-`p` subgroup `X`. -/
theorem line_le_of_le_E_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau2 M) {A : Subgroup G}
    (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXE : X ≤ E) :
    X ≤ A := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  -- `X ⊔ A` is a `p`-group: `A.subgroupOf E` is normal in `↥E` by part 1.
  haveI : (A.subgroupOf E).Normal := by
    constructor
    intro a ha g
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp
      (E_le_normalizer_of_tau2 hG h hp hA hAE g.2) (a : G)).mp ha
  have hsup_pg : IsPGroup p ↥(X.subgroupOf E ⊔ A.subgroupOf E : Subgroup ↥E) :=
    IsPGroup.to_sup_of_normal_right hX.1.isPGroup.comap_subtype
      hA.1.isPGroup.comap_subtype
  have hXA_pg : IsPGroup p ↥(X ⊔ A : Subgroup G) := by
    have hmap : (X.subgroupOf E ⊔ A.subgroupOf E).map E.subtype = X ⊔ A := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXE,
        Subgroup.map_subgroupOf_eq_of_le hAE]
    rw [← hmap]
    exact hsup_pg.map _
  -- a Sylow `p`-subgroup of `M` containing `X ⊔ A`.
  have hXAM : X ⊔ A ≤ M := sup_le (hXE.trans h.E_le) hAM
  obtain ⟨PM, hPM⟩ := hXA_pg.comap_subtype.exists_le_sylow (G := M)
  set P : Subgroup G := (PM : Subgroup ↥M).map M.subtype with hPdef
  have hXAP : X ⊔ A ≤ P := by
    rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hXAM]
    exact Subgroup.map_mono hPM
  have hP_le : P ≤ M := Subgroup.map_subtype_le _
  have hPpg : IsPGroup p ↥P := by rw [hPdef]; exact PM.isPGroup'.map _
  have hPsyl : ∀ R : Subgroup G, P ≤ R → R ≤ M → IsPGroup p ↥R → R = P := by
    intro R hPR hRM hRpg
    have hle : (PM : Subgroup ↥M) ≤ R.subgroupOf M := by
      refine le_trans (fun y hy => Subgroup.mem_subgroupOf.mpr ?_)
        (Subgroup.comap_mono hPR)
      rw [hPdef]
      exact Subgroup.mem_map_of_mem _ hy
    have heq : R.subgroupOf M = PM := PM.3 hRpg.comap_subtype hle
    rw [← Subgroup.map_subgroupOf_eq_of_le hRM, heq, hPdef]
  have homega := (omega1_eq_of_tau2 hG h.mem_maximal hp hA hAM hPpg
    (le_sup_right.trans hXAP) hP_le hPsyl).1
  rw [homega]
  intro x hx
  have hxP : x ∈ P := hXAP (Subgroup.mem_sup_left hx)
  have hxp : x ^ p = 1 := by
    simpa using congrArg Subtype.val (hX.1.pow_eq_one ⟨x, hx⟩)
  refine ⟨⟨x, hxP⟩, ?_, rfl⟩
  apply Subgroup.subset_closure
  show (⟨x, hxP⟩ : ↥P) ^ (p ^ 1) = 1
  rw [pow_one]
  exact Subtype.ext (by simpa using hxp)

/-- **BG Corollary 12.6(b)** (mmd L3194-3196): `C_G(A) ≤ E`, `N_M(A) = E`, and
`N_G(A) ⊄ M`. The Dedekind decomposition `N_M(A) = N_{M_σ}(A)·E` reduces to
`N_{M_σ}(A) = C_{M_σ}(A) = 1` (commutators land in `A ⊓ M_σ = 1`, then
Theorem 12.5(d)); `C_G(A) ≤ M` is Proposition 12.4(a); and `N_G(P) ≤ N_G(Ω₁(P)) =
N_G(A)` with `N_G(P) ⊄ M` from Theorem 12.5(b). -/
theorem centralizer_le_E_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau2 M) {A : Subgroup G}
    (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    Subgroup.centralizer (A : Set G) ≤ E ∧
    M ⊓ Subgroup.normalizer (A : Set G) = E ∧
    ¬ (Subgroup.normalizer (A : Set G) ≤ M) := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  have h125 := Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM
  have hd := h125.2.2.2.1
  have hNMA : M ⊓ Subgroup.normalizer (A : Set G) = E := by
    refine le_antisymm ?_
      (le_inf h.E_le (E_le_normalizer_of_tau2 hG h hp hA hAE))
    rintro x ⟨hxM, hxN⟩
    haveI : ((S10.Msigma M).subgroupOf M).Normal := by
      rw [S10.Msigma_subgroupOf]; infer_instance
    have hMσM : S10.Msigma M ≤ M := S10.Msigma_le M
    have hsub : (⟨x, hxM⟩ : ↥M) ∈ (S10.Msigma M).subgroupOf M ⊔ E.subgroupOf M := by
      rw [← Subgroup.subgroupOf_sup hMσM h.E_le, h.E_compl_sup]
      exact Subgroup.mem_subgroupOf.mpr hxM
    have hsub' : (⟨x, hxM⟩ : ↥M) ∈
        ((S10.Msigma M).subgroupOf M : Set ↥M) * (E.subgroupOf M : Set ↥M) := by
      rw [← Subgroup.normal_mul]
      exact hsub
    obtain ⟨s, hs, e, he, hse⟩ := hsub'
    have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
    have heN : (e : G) ∈ Subgroup.normalizer (A : Set G) :=
      E_le_normalizer_of_tau2 hG h hp hA hAE heE
    have hseq : (s : G) = x * ((e : ↥M) : G)⁻¹ := by
      have h1 : (s : ↥M) = ⟨x, hxM⟩ * e⁻¹ := by rw [← hse]; group
      calc (s : G) = ((⟨x, hxM⟩ * e⁻¹ : ↥M) : G) := congrArg Subtype.val h1
        _ = x * ((e : ↥M) : G)⁻¹ := rfl
    have hsN : (s : G) ∈ Subgroup.normalizer (A : Set G) := by
      rw [hseq]
      exact Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ heN)
    have hsMσ : (s : G) ∈ S10.Msigma M := Subgroup.mem_subgroupOf.mp hs
    -- `s` centralizes `A`: commutators land in `A ⊓ M_σ = ⊥`.
    have hAMσ_bot : A ⊓ S10.Msigma M = ⊥ := by
      rw [← le_bot_iff, ← h.E_compl_inf]
      exact le_inf inf_le_right (inf_le_left.trans hAE)
    have hsC : (s : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haM : a ∈ M := hAM ha
      have h1 : a * (s : G) * a⁻¹ * (s : G)⁻¹ ∈ S10.Msigma M := by
        have h2 : a * (s : G) * a⁻¹ ∈ S10.Msigma M :=
          (Subgroup.mem_normalizer_iff.mp ((le_normalizer_opiCoreInG _ _) haM) _).mp hsMσ
        exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hsMσ)
      have h2 : a * (s : G) * a⁻¹ * (s : G)⁻¹ ∈ A := by
        have h3 : (s : G) * a⁻¹ * (s : G)⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp hsN a⁻¹).mp (A.inv_mem ha)
        have h4 : a * ((s : G) * a⁻¹ * (s : G)⁻¹) ∈ A := A.mul_mem ha h3
        simpa [mul_assoc] using h4
      have h5 : a * (s : G) * a⁻¹ * (s : G)⁻¹ ∈ A ⊓ S10.Msigma M := ⟨h2, h1⟩
      rw [hAMσ_bot, Subgroup.mem_bot] at h5
      calc a * (s : G) = (a * (s : G) * a⁻¹ * (s : G)⁻¹) * ((s : G) * a) := by group
        _ = (s : G) * a := by rw [h5, one_mul]
    have hsbot : (s : G) ∈ S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) :=
      ⟨hsMσ, hsC⟩
    rw [hd, Subgroup.mem_bot] at hsbot
    have hxe : (⟨x, hxM⟩ : ↥M) = e := by
      rw [← hse, show s = 1 from Subtype.ext hsbot]
      exact one_mul e
    have hxe' : x = ((e : ↥M) : G) := congrArg Subtype.val hxe
    rw [hxe']
    exact heE
  refine ⟨?_, hNMA, ?_⟩
  · have hCM : Subgroup.centralizer (A : Set G) ≤ M :=
      centralizer_le_of_elemAb_rank_two hG h.mem_maximal hA hAM
    rw [← hNMA]
    exact le_inf hCM (Subgroup.centralizer_le_normalizer _)
  · obtain ⟨P, hP_le, hPpg, hAP, hPsyl', hPnot⟩ := h125.2.1.2
    have homega := (omega1_eq_of_tau2 hG h.mem_maximal hp hA hAM hPpg hAP hP_le
      (fun R hPR hRM hRpg => (hPsyl' R hRM hRpg hPR).symm)).1
    intro hcon
    apply hPnot
    have hNP_NA : Subgroup.normalizer (P : Set G) ≤
        Subgroup.normalizer (A : Set G) := by
      have h1 := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
        (K := P) (W := Omega ↥P p 1)
      rwa [← homega] at h1
    exact hNP_NA.trans hcon

end OddOrder.BG.Ch3.S12
