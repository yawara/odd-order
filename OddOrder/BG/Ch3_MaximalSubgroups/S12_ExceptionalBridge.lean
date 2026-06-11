/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S10_LocalLemmasCore
import OddOrder.BG.Ch3_MaximalSubgroups.S11_MsigmaANormal
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1218

/-!
# BG §12: The exceptional bridge — Lemma 12.3 (+ Lemma 12.2(b))

**スコープ**: BG Chapter III §12, Lemma 12.2(b) σ-case + Lemma 12.3 (pp. 84-85,
mmd L3089-3123)。§11 (exceptional maximal subgroups) を §12 へ接続する橋で、
τ₂-cascade (12.4 → 12.5 → 12.6-12.16) の根。

## 主要結果

- `Hypothesis111.of_normalizer_le`: **BG Hypothesis 11.1 constructor** (mmd L2947-2957)。
  literal data (`M ∈ ℳ`, `p ∉ σ(M)`, `A₀ ∈ ℰ_p¹(M)`, `N_G(A₀) ⊆ M`, `A₀ ≤ A ∈ ℰ_p²(M)`)
  から Lemma 10.5 の導出データ (`P ∈ Syl_p(M)`, `N_G(P) ⊄ M`, `A ∈ ℰ_p*(G)`) を構成。
  `A ∈ ℰ_p*(G)` は `C_G(A) ⊆ C_G(A₀) ⊆ N_G(A₀) ⊆ M` + `r_p(M) = 2` から。
- `not_conj_of_mem_sigma_of_normalizer_le`: **BG Lemma 12.2(b)** (σ-case, mmd L3093):
  `p ∈ σ(M)`, `X` nonidentity `p`-subgroup of `M`, `N_G(X) ⊆ M* ≠ M` ⇒ `M*` は `M` と
  `G` 内で非共役。Theorem 10.1(b) の fusion transitivity による。
  (τ₁∪τ₃-case は cascade で未使用ゆえ消費側が現れた時点で追加する。)
- `normalizer_Malpha_sup_sylow_of_mem_sigma`: **BG Theorem 10.2(d) Sylow closure**:
  `p ∈ σ(M)`, `S ∈ Syl_p(M)` ⇒ `M_α S ⊴ M`。`M/M_α` 内で `S̄ ≤ F(M/M_α)` nilpotent の
  Sylow ゆえ characteristic。
- `commutator_le_inf_Msigma_of_normalizer_le`: **Lemma 12.3 engine** (mmd L3107-3111):
  `A`-不変 `p'`-部分群 `K ≤ M*` に対し `⁅A, K⁆ ≤ K ⊓ M*_σ`。
- `elemAb_centralizes_Msigma_meet` / `elemAb_centralizes_Malpha_meet`: **BG Lemma 12.3
  (a) / (b)** (mmd L3101-3123)。scaffold 版 `elemAb_centralizes_meet` (旧 S12_E) は
  場合分け仮定 (`p ∉ σ(M)` / `p ∈ σ(M) − α(M)`) と `M* ≠ M` を欠いた unfaithful な
  statement だったため、原典 faithful な 2 定理に置き換えた。
-/

namespace OddOrder.BG.Ch3

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

namespace S12

/-! ## 汎用 helper -/

/-- Conjugacy of subgroups is symmetric (in the `¬∃ g` form used by Lemma 10.12). -/
theorem not_conj_symm {M H : Subgroup G} (h : ¬ ∃ g : G, MulAut.conj g • M = H) :
    ¬ ∃ g : G, MulAut.conj g • H = M := by
  rintro ⟨g, hg⟩
  exact h ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩

/-- A normal subgroup `W ⊴ ↥M` has its image `W.map M.subtype` normalized by `M`. -/
theorem le_normalizer_map_subtype_of_normal {M : Subgroup G} {W : Subgroup ↥M}
    (hW : W.Normal) :
    M ≤ Subgroup.normalizer ((W.map M.subtype : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨w, hwW, rfl⟩
    exact ⟨⟨m, hm⟩ * w * ⟨m, hm⟩⁻¹, hW.conj_mem w hwW ⟨m, hm⟩, rfl⟩
  · rintro ⟨w, hwW, hwx⟩
    refine ⟨⟨m, hm⟩⁻¹ * w * ⟨m, hm⟩, ?_, ?_⟩
    · have h1 := hW.conj_mem w hwW ⟨m, hm⟩⁻¹
      rwa [inv_inv] at h1
    · have hsub : M.subtype ⟨m, hm⟩ = m := rfl
      rw [map_mul, map_mul, map_inv, hsub, hwx]
      group

/-- **Coprime sup-reduction**: if `P` normalizes `N` and `H ≤ N ⊔ P` has order coprime to
`|P|`, then `H ≤ N`. (In `L = N ⊔ P` the subgroup `N` is normal and `L/N` is an image of
`P`, so the image of `H` in `L/N` has order dividing `gcd(|H|, |P|) = 1`.) -/
theorem le_of_le_sup_of_coprime_card [Finite G] {N P H : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hH : H ≤ N ⊔ P)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥P)) : H ≤ N := by
  classical
  set L : Subgroup G := N ⊔ P with hLdef
  have hNL : N ≤ L := le_sup_left
  have hPL : P ≤ L := le_sup_right
  have hL_norm : L ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hPN
  haveI hNsub_norm : (N.subgroupOf L).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hL_norm g.2) (n : G)).mp hn
  set π : ↥L →* ↥L ⧸ N.subgroupOf L := QuotientGroup.mk' (N.subgroupOf L) with hπdef
  -- the quotient is the image of `P`.
  have htop : (P.subgroupOf L).map π = ⊤ := by
    have h1 : ((N.subgroupOf L) ⊔ (P.subgroupOf L)).map π = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hNL hPL, ← hLdef, Subgroup.subgroupOf_self,
        ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    have h2 : (N.subgroupOf L).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk']
    rwa [Subgroup.map_sup, h2, bot_sup_eq] at h1
  have hcard_quot : Nat.card (↥L ⧸ N.subgroupOf L) ∣ Nat.card ↥P := by
    calc Nat.card (↥L ⧸ N.subgroupOf L)
        = Nat.card ↥(⊤ : Subgroup (↥L ⧸ N.subgroupOf L)) :=
          (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
      _ = Nat.card ↥((P.subgroupOf L).map π) := by rw [htop]
      _ ∣ Nat.card ↥(P.subgroupOf L) := Subgroup.card_map_dvd _ π
      _ = Nat.card ↥P := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  -- the image of `H` is trivial.
  have hHbot : (H.subgroupOf L).map π = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥((H.subgroupOf L).map π) ∣ Nat.card ↥H := by
      calc Nat.card ↥((H.subgroupOf L).map π) ∣ Nat.card ↥(H.subgroupOf L) :=
            Subgroup.card_map_dvd _ π
        _ = Nat.card ↥H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
    have h2 : Nat.card ↥((H.subgroupOf L).map π) ∣ Nat.card ↥P :=
      (Subgroup.card_subgroup_dvd_card _).trans hcard_quot
    exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2)
  intro h hh
  have hmem : (⟨h, hH hh⟩ : ↥L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh
  have hker : H.subgroupOf L ≤ π.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    exact hHbot
  have h2 : (⟨h, hH hh⟩ : ↥L) ∈ N.subgroupOf L := by
    have := hker hmem
    rwa [hπdef, QuotientGroup.ker_mk'] at this
  exact Subgroup.mem_subgroupOf.mp h2

/-- A nontrivial `p`-group is a `π`-subgroup whenever `p ∈ π`. -/
theorem isPiSubgroup_of_isPGroup_of_mem [Finite G] {π : Set ℕ} {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (hX : IsPGroup p ↥X) (hp : p ∈ π) :
    Subgroup.IsPiSubgroup π X := by
  intro q hq
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk] at hq
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hdvd : q ∣ p ^ k := (Nat.mem_primeFactors.mp hq).2.1
  have hqp : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq_prime Fact.out).mp (hq_prime.dvd_of_dvd_pow hdvd)
  rwa [hqp]

end S12

namespace S11

/-! ## Hypothesis 11.1 constructor (mmd L2947-2957) -/

/-- **BG Hypothesis 11.1 constructor**: from the literal hypothesis data — `M ∈ ℳ`,
`p ∉ σ(M)`, `A₀ ∈ ℰ_p¹(M)`, `N_G(A₀) ⊆ M` — together with a given
`A ∈ ℰ_p²(M)` containing `A₀`, produce the §11 standing assumption `Hypothesis111`.
The derived data follows BG (mmd L2951-2957): `r_p(M) = 2` is Lemma 10.5
(`pRank_eq_two_of_normalizer_le`); `P` is any Sylow `p`-subgroup of `M` containing `A`;
`N_G(P) ⊄ M` holds because `p ∉ σ(M)`; and `A ∈ ℰ_p*(G)` because any elementary abelian
`F ⊇ A` lies in `C_G(A) ⊆ C_G(A₀) ⊆ N_G(A₀) ⊆ M` and `r_p(M) = 2`. -/
theorem Hypothesis111.of_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∉ S10.sigma M) {A₀ A : Subgroup G}
    (hA₀ : A₀ ∈ elemAbelianOfRank G p 1) (hN : Subgroup.normalizer (A₀ : Set G) ≤ M)
    (hA : A ∈ elemAbelianOfRank G p 2) (hA₀A : A₀ ≤ A) (hAM : A ≤ M) :
    ∃ P : Subgroup G, Hypothesis111 M p A₀ A P := by
  classical
  have hA₀M : A₀ ≤ M := Subgroup.le_normalizer.trans hN
  -- Lemma 10.5: `r_p(M) = 2`.
  obtain ⟨hr2, -, -⟩ := S10.pRank_eq_two_of_normalizer_le hG hM hp hA₀ hN
  -- a Sylow `p`-subgroup `P` of `M` containing `A`.
  have hApg : IsPGroup p ↥A := hA.1.isPGroup
  obtain ⟨PM, hAPM⟩ := hApg.comap_subtype.exists_le_sylow (G := M)
  set P : Subgroup G := (PM : Subgroup ↥M).map M.subtype with hPdef
  have hPM_le : P ≤ M := Subgroup.map_subtype_le _
  have hAP : A ≤ P := by
    rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hAM]
    exact Subgroup.map_mono hAPM
  have hPpg : IsPGroup p ↥P := by
    rw [hPdef]; exact PM.isPGroup'.map _
  -- `P` is `p`-maximal in `M`.
  have hPsyl : ∀ R : Subgroup G, P ≤ R → R ≤ M → IsPGroup p ↥R → R = P := by
    intro R hPR hRM hRpg
    have hle : (PM : Subgroup ↥M) ≤ R.subgroupOf M := by
      refine le_trans (fun x hx => Subgroup.mem_subgroupOf.mpr ?_) (Subgroup.comap_mono hPR)
      rw [hPdef]
      exact Subgroup.mem_map_of_mem _ hx
    have heq : R.subgroupOf M = PM := PM.3 hRpg.comap_subtype hle
    rw [← Subgroup.map_subgroupOf_eq_of_le hRM, heq, hPdef]
  -- `N_G(P) ⊄ M` since `p ∉ σ(M)`.
  have hPnot : ¬ Subgroup.normalizer (P : Set G) ≤ M := by
    intro hcon
    apply hp
    rw [S10.mem_sigma_iff]
    refine ⟨?_, PM, ?_⟩
    · have hdvd : p ∣ Nat.card ↥M := by
        have h1 : (p : ℕ) ∣ Nat.card ↥A := by
          rw [hA.2]; exact dvd_pow_self p two_ne_zero
        exact h1.trans (Subgroup.card_dvd_of_le hAM)
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
    · rw [← hPdef]; exact hcon
  -- `A ∈ ℰ_p*(G)`: any elementary abelian `F ⊇ A` lies in `M`, and `r_p(M) = 2`.
  have hAmax : IsMaximalElementaryAbelian p A := by
    refine ⟨hA.1, fun F hF hAF => ?_⟩
    by_contra hne
    have hFM : F ≤ M := by
      refine le_trans (fun f hf => ?_) ((Subgroup.centralizer_le_normalizer _).trans hN)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      simpa using congrArg Subtype.val (hF.comm (⟨a, hAF (hA₀A ha)⟩ : ↥F) ⟨f, hf⟩)
    have hAltF : A < F := lt_of_le_of_ne hAF (fun h => hne h.symm)
    have hcard_lt : Nat.card ↥A < Nat.card ↥F := by
      refine lt_of_le_of_ne
        (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hAltF.le))
        (fun hcard => ?_)
      exact hne ((Subgroup.eq_of_le_of_card_ge hAF hcard.ge).symm)
    obtain ⟨k, hk⟩ := hF.isPGroup.exists_card_eq
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have hle : Nat.card ↥F ≤ p ^ 2 := by
        rw [hk]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
      rw [hA.2] at hcard_lt
      omega
    have hFsub_ea : (F.subgroupOf M).IsElementaryAbelian p :=
      OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hFM).symm hF
    have hle := le_pRank (G := ↥M) (F.subgroupOf M) hFsub_ea
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv, hk,
      Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
    omega
  exact ⟨P, hM, Fact.out, hp, hA₀, hA₀M, hN, hA, hAM, hA₀A, hPpg, hAP, hPM_le, hPsyl,
    hPnot, hAmax⟩

end S11

namespace S12

/-! ## Lemma 12.2(b), σ-case (mmd L3093, proof L3100) -/

/-- **BG Lemma 12.2(b)** (σ-case): if `p ∈ σ(M)`, `X` is a nonidentity `p`-subgroup of `M`
with `N_G(X) ⊆ M* ≠ M`, then `M*` is not conjugate to `M` in `G`. By Theorem 10.1(b),
`C_G(X)` acts transitively on `{M^g | X ⊆ M^g}`; if `M* = M^h` then some `c ∈ C_G(X)`
conjugates `M*` to `M`, but `c ∈ C_G(X) ⊆ N_G(X) ⊆ M*` fixes `M*`, so `M* = M`. -/
theorem not_conj_of_mem_sigma_of_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ S10.sigma M) {X : Subgroup G} (hXM : X ≤ M) (hXne : X ≠ ⊥)
    (hXp : IsPGroup p ↥X) (hN : Subgroup.normalizer (X : Set G) ≤ Mstar)
    (hMne : Mstar ≠ M) :
    ¬ ∃ g : G, MulAut.conj g • M = Mstar := by
  rintro ⟨h, hh⟩
  have hb := (S10.fusion_control_of_mem_sigma hG hM hp hXne hXp).2.1
  have hXMstar : X ≤ MulAut.conj h • M := by
    rw [hh]; exact Subgroup.le_normalizer.trans hN
  have hXM1 : X ≤ MulAut.conj (1 : G) • M := by
    rw [map_one, one_smul]; exact hXM
  obtain ⟨c, hcC, hc⟩ := hb h 1 hXMstar hXM1
  rw [map_one, one_smul, hh] at hc
  have hcMstar : c ∈ Mstar := hN (Subgroup.centralizer_le_normalizer _ hcC)
  have hfix : MulAut.conj c • Mstar = Mstar :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hcMstar)
  rw [hfix] at hc
  exact hMne hc

/-! ## Theorem 10.2(d) Sylow closure: `M_α S ⊴ M` for `p ∈ σ(M)` -/

/-- **BG Theorem 10.2(d), Sylow `p`-closure** (used in the proof of Lemma 12.3(a),
mmd L3115-3119): for `p ∈ σ(M)` and a Sylow `p`-subgroup `S` of `M`, the join
`M_α ⊔ S` is normalized by `M`. In the quotient `M/M_α` the image of `S` is a Sylow
`p`-subgroup lying inside the nilpotent Fitting subgroup `F(M/M_α)` (because `S ≤ M_σ`
and `M_σ M_α/M_α ≤ F(M/M_α)` by Theorem 10.2(d)), hence is normal in `M/M_α`;
its preimage `M_α ⊔ S` is therefore normal in `M`. -/
theorem normalizer_Malpha_sup_sylow_of_mem_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ S10.sigma M) (SM : Sylow p ↥M) :
    M ≤ Subgroup.normalizer
      ((S10.Malpha M ⊔ (SM : Subgroup ↥M).map M.subtype : Subgroup G) : Set G) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  set N : Subgroup ↥M := (S10.Malpha M).subgroupOf M with hNdef
  haveI hN_norm : N.Normal := by rw [hNdef, S10.Malpha_subgroupOf]; infer_instance
  set π : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N with hπdef
  -- the image of `SM` is a Sylow `p`-subgroup of the quotient.
  set Sb : Sylow p (↥M ⧸ N) := SM.mapSurjective (QuotientGroup.mk'_surjective N) with hSbdef
  have hSb_coe : (Sb : Subgroup (↥M ⧸ N)) = (SM : Subgroup ↥M).map π := rfl
  -- `SM ≤ M_σ.subgroupOf M` since `p ∈ σ(M)`.
  have hSM_Mσ : (SM : Subgroup ↥M) ≤ (S10.Msigma M).subgroupOf M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact S10.sigma_subgroup_le_Msigma_of_isHall
      (S10.isHall_Msigma_Malpha hG hM).1 (Subgroup.map_subtype_le _)
      (isPiSubgroup_of_isPGroup_of_mem (SM.isPGroup'.map _) hp)
      (Subgroup.mem_map_of_mem _ hx)
  -- hence `Sb ≤ F(M/M_α)`, which is nilpotent.
  have hSb_F : (Sb : Subgroup (↥M ⧸ N)) ≤ Ch01.fitting (↥M ⧸ N) := by
    rw [hSb_coe]
    exact (Subgroup.map_mono hSM_Mσ).trans (S10.Msigma_quotient_Malpha_le_fitting hG hM)
  -- a Sylow subgroup inside a nilpotent normal subgroup is normal.
  set SbF : Sylow p ↥(Ch01.fitting (↥M ⧸ N)) := Sb.subtype hSb_F with hSbFdef
  have hSbF_norm : (SbF : Subgroup ↥(Ch01.fitting (↥M ⧸ N))).Normal := by
    have htfae := (isNilpotent_of_finite_tfae (G := ↥(Ch01.fitting (↥M ⧸ N)))).out 0 3
    exact htfae.mp inferInstance p ⟨Fact.out⟩ SbF
  haveI hSbF_char : (SbF : Subgroup ↥(Ch01.fitting (↥M ⧸ N))).Characteristic :=
    Sylow.characteristic_of_normal SbF hSbF_norm
  have hSb_norm : (Sb : Subgroup (↥M ⧸ N)).Normal := by
    have h1 := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
      (K := Ch01.fitting (↥M ⧸ N)) (W := (SbF : Subgroup ↥(Ch01.fitting (↥M ⧸ N))))
    have h2 : ((SbF : Subgroup ↥(Ch01.fitting (↥M ⧸ N))).map
        (Ch01.fitting (↥M ⧸ N)).subtype) = (Sb : Subgroup (↥M ⧸ N)) := by
      rw [hSbFdef, Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSb_F]
    rw [h2] at h1
    have h3 : Subgroup.normalizer
        ((Ch01.fitting (↥M ⧸ N) : Subgroup (↥M ⧸ N)) : Set (↥M ⧸ N)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (Ch01.fitting.normal (↥M ⧸ N))
    constructor
    intro n hn g
    have hg : g ∈ Subgroup.normalizer ((Sb : Subgroup (↥M ⧸ N)) : Set (↥M ⧸ N)) :=
      h1 (h3 ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  -- pull back: `SM ⊔ N` is normal in `↥M`, and maps to `S ⊔ M_α` in `G`.
  have hcomap_norm : ((Sb : Subgroup (↥M ⧸ N)).comap π).Normal := hSb_norm.comap π
  have hcomap_eq : (Sb : Subgroup (↥M ⧸ N)).comap π = (SM : Subgroup ↥M) ⊔ N := by
    rw [hSb_coe, Subgroup.comap_map_eq, hπdef, QuotientGroup.ker_mk']
  have htransport := le_normalizer_map_subtype_of_normal (hcomap_eq ▸ hcomap_norm)
  have hmap_eq : ((SM : Subgroup ↥M) ⊔ N).map M.subtype
      = S10.Malpha M ⊔ (SM : Subgroup ↥M).map M.subtype := by
    rw [Subgroup.map_sup, hNdef, Subgroup.map_subgroupOf_eq_of_le (S10.Malpha_le M), sup_comm]
  rwa [hmap_eq] at htransport

/-! ## Lemma 12.3 engine (mmd L3107-3111) -/

/-- **Lemma 12.3, commutator engine** (mmd L3107-3111): whether `p ∈ σ(M*)` (then
`A ≤ M*_σ`) or not (then `M*_σ A ⊴ M*` by Theorem 11.7 via Hypothesis 11.1), the join
`M*_σ ⊔ A` is normalized by `M*`. Consequently every `A`-invariant `p'`-subgroup
`K ≤ M*` satisfies `⁅A, K⁆ ≤ K ⊓ M*_σ A ≤ K ⊓ M*_σ`. -/
theorem commutator_le_inf_Msigma_of_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {Mstar : Subgroup G} (hMstar : Mstar ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    {A₀ A : Subgroup G} (hA₀ : A₀ ∈ elemAbelianOfRank G p 1)
    (hN : Subgroup.normalizer (A₀ : Set G) ≤ Mstar)
    (hA : A ∈ elemAbelianOfRank G p 2) (hA₀A : A₀ ≤ A) (hAMstar : A ≤ Mstar)
    {K : Subgroup G} (hKM : K ≤ Mstar) (hKinv : A ≤ Subgroup.normalizer (K : Set G))
    (hKp : ¬ p ∣ Nat.card ↥K) :
    ⁅A, K⁆ ≤ K ⊓ S10.Msigma Mstar := by
  classical
  -- `M* ≤ N_G(M*_σ ⊔ A)` in either case.
  have hsup : Mstar ≤ Subgroup.normalizer ((S10.Msigma Mstar ⊔ A : Subgroup G) : Set G) := by
    by_cases hpσ : p ∈ S10.sigma Mstar
    · have hAMσ : A ≤ S10.Msigma Mstar :=
        S10.sigma_subgroup_le_Msigma_of_isHall (S10.isHall_Msigma_Malpha hG hMstar).1
          hAMstar (isPiSubgroup_of_isPGroup_of_mem hA.1.isPGroup hpσ)
      rw [sup_eq_left.mpr hAMσ]
      exact le_normalizer_opiCoreInG _ _
    · obtain ⟨P, h111⟩ :=
        S11.Hypothesis111.of_normalizer_le hG hMstar hpσ hA₀ hN hA hA₀A hAMstar
      exact S11.MsigmaA_normal hG h111
  -- elementwise: `⁅A, K⁆ ≤ K ⊓ (M*_σ ⊔ A)`.
  have h1 : ⁅A, K⁆ ≤ K ⊓ (S10.Msigma Mstar ⊔ A) := by
    rw [Subgroup.commutator_le]
    intro a ha k hk
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h2 : a * k * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKinv ha) k).mp hk
      have h3 : a * k * a⁻¹ * k⁻¹ ∈ K := K.mul_mem h2 (K.inv_mem hk)
      rwa [commutatorElement_def]
    · have hkM : k ∈ Mstar := hKM hk
      have h2 : k * a⁻¹ * k⁻¹ ∈ S10.Msigma Mstar ⊔ A :=
        (Subgroup.mem_normalizer_iff.mp (hsup hkM) a⁻¹).mp
          (Subgroup.mem_sup_right (A.inv_mem ha))
      have h3 : a * (k * a⁻¹ * k⁻¹) ∈ S10.Msigma Mstar ⊔ A :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) h2
      rw [commutatorElement_def]
      simpa [mul_assoc] using h3
  -- coprime reduction: `K ⊓ (M*_σ ⊔ A) ≤ M*_σ`.
  refine h1.trans (le_inf inf_le_left ?_)
  have hAnorm : A ≤ Subgroup.normalizer ((S10.Msigma Mstar : Subgroup G) : Set G) :=
    hAMstar.trans (le_normalizer_opiCoreInG _ _)
  refine le_of_le_sup_of_coprime_card hAnorm inf_le_right ?_
  have hnp : ¬ p ∣ Nat.card ↥(K ⊓ (S10.Msigma Mstar ⊔ A) : Subgroup G) :=
    fun h => hKp (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  rw [hA.2]
  exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnp).symm.pow_right 2

/-! ## Lemma 12.3 (mmd L3101-3123) -/

/-- **BG Lemma 12.3(a)** (mmd L3101): `M* ∈ ℳ − {M}`, `A ∈ ℰ_p²(M ∩ M*)`,
`A₀ ∈ ℰ¹(A)` with `N_G(A₀) ⊆ M*`, and `p ∉ σ(M)`. Then `A` centralizes `M_σ ∩ M*`.

Proof (mmd L3113-3123): let `K = M_σ ∩ M*`, an `A`-invariant `p'`-subgroup of `M*`.
If `p ∉ σ(M*)`, the engine gives `⁅A,K⁆ ≤ M_σ ∩ M*_σ`, which is `⊥` by Corollary 11.4
(else `M* = M`). If `p ∈ σ(M*)`, then `M*` is not conjugate to `M` (σ-sets differ),
`A ≤ S` for a Sylow `p`-subgroup `S` of `M*` with `M*_α S ⊴ M*` (Theorem 10.2(d)
Sylow closure), so `⁅A,K⁆ ≤ K ⊓ M*_α S ≤ M*_α ⊓ M_σ = ⊥` by Lemma 10.12(a). -/
theorem elemAb_centralizes_Msigma_meet [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hMstar : Mstar ∈ maximalSubgroups G) (hne : Mstar ≠ M) {p : ℕ} [Fact p.Prime]
    (hp : p ∉ S10.sigma M) {A A₀ : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    (hAM : A ≤ M ⊓ Mstar) (hA₀ : A₀ ∈ elemAbelianOfRank G p 1) (hA₀A : A₀ ≤ A)
    (hN : Subgroup.normalizer (A₀ : Set G) ≤ Mstar) :
    A ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) := by
  classical
  have hAM' : A ≤ M := hAM.trans inf_le_left
  have hAMstar : A ≤ Mstar := hAM.trans inf_le_right
  set K : Subgroup G := S10.Msigma M ⊓ Mstar with hKdef
  have hKMstar : K ≤ Mstar := inf_le_right
  have hKMσ : K ≤ S10.Msigma M := inf_le_left
  have hKinv : A ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_inf (hAM'.trans (le_normalizer_opiCoreInG _ _))
      (hAMstar.trans Subgroup.le_normalizer)
  have hKp : ¬ p ∣ Nat.card ↥K := by
    intro hdvd
    have h1 : p ∣ Nat.card ↥(S10.Msigma M) := hdvd.trans (Subgroup.card_dvd_of_le hKMσ)
    exact hp (S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, h1, Nat.card_pos.ne'⟩))
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  by_cases hpσ : p ∈ S10.sigma Mstar
  · -- `p ∈ σ(M*)`: `M*` is not conjugate to `M`, and `⁅A,K⁆ ≤ M*_α ⊓ M_σ = ⊥`.
    have hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar := by
      rintro ⟨g, hg⟩
      apply hp
      have h1 : p ∈ S10.sigma (MulAut.conj g⁻¹ • (MulAut.conj g • M)) :=
        S10.sigma_conj g⁻¹ (hg ▸ hpσ)
      rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
    have h1012 := ((S10.disjoint_of_not_conj hG hMstar hM (not_conj_symm hnc)).1).1
    -- `A ≤ M*_σ` and a Sylow `p`-subgroup `S ⊇ A` of `M*`.
    have hApg : IsPGroup p ↥A := hA.1.isPGroup
    obtain ⟨SM, hASM⟩ := hApg.comap_subtype.exists_le_sylow (G := Mstar)
    set S : Subgroup G := (SM : Subgroup ↥Mstar).map Mstar.subtype with hSdef
    have hAS : A ≤ S := by
      rw [hSdef, ← Subgroup.map_subgroupOf_eq_of_le hAMstar]
      exact Subgroup.map_mono hASM
    have hT := normalizer_Malpha_sup_sylow_of_mem_sigma hG hMstar hpσ SM
    -- `⁅A,K⁆ ≤ K ⊓ (M*_α ⊔ S)` elementwise.
    have hcomm_le : ⁅A, K⁆ ≤ K ⊓ (S10.Malpha Mstar ⊔ S) := by
      rw [Subgroup.commutator_le]
      intro a ha k hk
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h2 : a * k * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKinv ha) k).mp hk
        have h3 : a * k * a⁻¹ * k⁻¹ ∈ K := K.mul_mem h2 (K.inv_mem hk)
        rwa [commutatorElement_def]
      · have hkM : k ∈ Mstar := hKMstar hk
        have h2 : k * a⁻¹ * k⁻¹ ∈ S10.Malpha Mstar ⊔ S :=
          (Subgroup.mem_normalizer_iff.mp (hT hkM) a⁻¹).mp
            (Subgroup.mem_sup_right (S.inv_mem (hAS ha)))
        have h3 : a * (k * a⁻¹ * k⁻¹) ∈ S10.Malpha Mstar ⊔ S :=
          Subgroup.mul_mem _ (Subgroup.mem_sup_right (hAS ha)) h2
        rw [commutatorElement_def]
        simpa [mul_assoc] using h3
    -- coprime reduction to `M*_α`, then Lemma 10.12(a).
    have hred : K ⊓ (S10.Malpha Mstar ⊔ S) ≤ S10.Malpha Mstar := by
      refine le_of_le_sup_of_coprime_card
        ((Subgroup.map_subtype_le _).trans (le_normalizer_opiCoreInG _ _)) inf_le_right ?_
      have hnp : ¬ p ∣ Nat.card ↥(K ⊓ (S10.Malpha Mstar ⊔ S) : Subgroup G) :=
        fun h => hKp (h.trans (Subgroup.card_dvd_of_le inf_le_left))
      obtain ⟨k, hk⟩ := (SM.isPGroup'.map Mstar.subtype).exists_card_eq
      rw [← hSdef] at hk
      rw [hk]
      exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnp).symm.pow_right k
    have hfin : ⁅A, K⁆ ≤ S10.Malpha Mstar ⊓ S10.Msigma M :=
      le_inf (hcomm_le.trans hred) ((hcomm_le.trans inf_le_left).trans hKMσ)
    rw [← le_bot_iff, ← h1012]
    exact hfin
  · -- `p ∉ σ(M*)`: engine + Corollary 11.4.
    have heng := commutator_le_inf_Msigma_of_normalizer_le hG hMstar hA₀ hN hA hA₀A
      hAMstar hKMstar hKinv hKp
    rcases eq_or_ne ⁅A, K⁆ ⊥ with hbot | hne_bot
    · exact hbot
    · exfalso
      obtain ⟨P, h111⟩ :=
        S11.Hypothesis111.of_normalizer_le hG hMstar hpσ hA₀ hN hA hA₀A hAMstar
      have hmeet : S10.Msigma Mstar ⊓ S10.Msigma M ≠ ⊥ := by
        intro hmeet_bot
        apply hne_bot
        rw [← le_bot_iff, ← hmeet_bot]
        exact le_inf (heng.trans inf_le_right) (heng.trans (inf_le_left.trans hKMσ))
      exact hne (S11.eq_of_Msigma_meet_Hsigma hG h111
        (mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hAM'⟩) hmeet)

/-- **BG Lemma 12.3(b)** (mmd L3103): `M* ∈ ℳ − {M}`, `A ∈ ℰ_p²(M ∩ M*)`,
`A₀ ∈ ℰ¹(A)` with `N_G(A₀) ⊆ M*`, and `p ∈ σ(M) − α(M)`. Then `A` centralizes
`M_α ∩ M*`.

Proof (mmd L3113): `K = M_α ∩ M*` is an `A`-invariant `p'`-subgroup of `M*`
(`p ∉ α(M)`), so the engine gives `⁅A,K⁆ ≤ K ⊓ M*_σ ≤ M_α ⊓ M*_σ`. By Lemma 12.2(b)
`M*` is not conjugate to `M`, so `M_α ⊓ M*_σ = ⊥` by Lemma 10.12(a). -/
theorem elemAb_centralizes_Malpha_meet [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hMstar : Mstar ∈ maximalSubgroups G) (hne : Mstar ≠ M) {p : ℕ} [Fact p.Prime]
    (hpσ : p ∈ S10.sigma M) (hpα : p ∉ S10.alpha M) {A A₀ : Subgroup G}
    (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M ⊓ Mstar)
    (hA₀ : A₀ ∈ elemAbelianOfRank G p 1) (hA₀A : A₀ ≤ A)
    (hN : Subgroup.normalizer (A₀ : Set G) ≤ Mstar) :
    A ≤ Subgroup.centralizer ((S10.Malpha M ⊓ Mstar : Subgroup G) : Set G) := by
  classical
  have hAM' : A ≤ M := hAM.trans inf_le_left
  have hAMstar : A ≤ Mstar := hAM.trans inf_le_right
  set K : Subgroup G := S10.Malpha M ⊓ Mstar with hKdef
  have hKMstar : K ≤ Mstar := inf_le_right
  have hKMα : K ≤ S10.Malpha M := inf_le_left
  have hKinv : A ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_inf (hAM'.trans (le_normalizer_opiCoreInG _ _))
      (hAMstar.trans Subgroup.le_normalizer)
  have hKp : ¬ p ∣ Nat.card ↥K := by
    intro hdvd
    have h1 : p ∣ Nat.card ↥(S10.Malpha M) := hdvd.trans (Subgroup.card_dvd_of_le hKMα)
    exact hpα (S10.Malpha_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, h1, Nat.card_pos.ne'⟩))
  -- non-conjugacy via Lemma 12.2(b) with `X = A₀`.
  have hA₀M : A₀ ≤ M := hA₀A.trans hAM'
  have hA₀ne : A₀ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A₀ = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hA₀.2, pow_one] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hnc := not_conj_of_mem_sigma_of_normalizer_le hG hM hpσ hA₀M hA₀ne
    hA₀.1.isPGroup hN hne
  have h1012 := ((S10.disjoint_of_not_conj hG hM hMstar hnc).1).1
  -- engine + Lemma 10.12(a).
  have heng := commutator_le_inf_Msigma_of_normalizer_le hG hMstar hA₀ hN hA hA₀A
    hAMstar hKMstar hKinv hKp
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← le_bot_iff, ← h1012]
  exact le_inf ((heng.trans inf_le_left).trans hKMα) (heng.trans inf_le_right)

end S12

end OddOrder.BG.Ch3
