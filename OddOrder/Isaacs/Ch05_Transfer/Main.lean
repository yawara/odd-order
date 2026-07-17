/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Basic
import OddOrder.Isaacs.Ch05_Transfer.Dietzmann
import OddOrder.Isaacs.Ch05_Transfer.NilpotentMaximal
import OddOrder.Isaacs.Ch05_Transfer.SylowTwoDirectFactor

/-!
# TAIL

Prefix-split from `OddOrder.Isaacs.Ch05_Transfer.Main` (2000-line limit, issue 0103 第 2 パス).
-/
open scoped commutatorElement
open scoped IsMulCommutative -- rc2: IsMulCommutative→CommGroup/Monoid now scoped

namespace OddOrder.Isaacs.Ch05
open Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5E: Frobenius normal p-complement (pp. 173-180) -/

/-! ### Isaacs §5E (Frobenius normal p-complement)

**FT クリティカル**. mathlib 未収載で新規実装が必要.

- **Def** `HasNormalPComplement p G` — 「G は normal p-complement を持つ」(§5C で導入済み).
- **Thm 5.25** (Sylow controls own fusion ⇔ normal p-comp): ✅ 完成.
  `controlsOwnFusion_of_hasNormalPComplement` + `hasNormalPComplement_of_controlsOwnFusion`.
- **Thm 5.26 Frobenius** (3 同値条件): ✅ 完成 (Lem 5.27 + Lem 5.28 + 5.25 経由).
- **Lem 5.27** (1 ⇒ 2 ⇒ 3 易方向): ✅ 完成. Part 1 (`hasNormalPComplement_of_subgroup`) +
  Part 2 (`isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement`).
- **Lem 5.28** (3 ⇒ Sylow 共役 via C_G(P ⊓ Q)): ✅ 完成 (sorry-free).
  helper `sylow_sup_normal_eq_top_of_quot_isPGroup` + `lt_normalizer_of_pgroup_of_lt_top`.
  main body Steps 1-11 全実装: P ⊓ N > D, Sylow S/T/R 設定, N=SC 分解,
  Sylow II in ↥N, T = yC • S, conjugation translation to G, index strict ineq,
  二回 IH chain (P, R) と (yR, Q), 結合 c = x · yC⁻¹ · z.
- **Cor 5.29** (q ∤ p^e-1 ⇒ normal p-comp): ✅ 完成 (5.26 + p-group action).
- **Cor 5.30** (p odd, 全 order-p 中心 ⇒ normal p-comp): ✅ 完成 (Ch.4 §4D Thm 4.36). -/

/-- If `A^p(G)=G`, then a Sylow p-subgroup is equal to its focal subgroup.

This packages only the standard `A^p` consequence of the focal subgroup theorem, avoiding a
separate public bridge through `G'`. -/
lemma sylow_focalSubgroup_eq_self_of_APrime_eq_top [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hA : APrime p G = ⊤) :
    P.focalSubgroup = (P : Subgroup G) := by
  have hker_top : P.transferFocal.ker = ⊤ := by
    apply eq_top_iff.mpr
    simpa [hA] using APrime_le_transferFocal_ker (G := G) (p := p) P
  rw [← Subgroup.ker_transferFocal_inf_eq_focalSubgroup P, hker_top, top_inf_eq]

/-- **Isaacs Thm 5.25 proof step**: if `N = O^p(G)`, then `A^p(N)=N`.

Isaacs p.173 uses that `A^p(N)` is characteristic in `N`, hence normal in `G`, and that
`|G:A^p(N)| = |G:N| · |N:A^p(N)|` is a p-power. Minimality of `O^p(G)` then gives
`N ≤ A^p(N).map subtype ≤ N`, so `A^p(N)=N` internally. -/
lemma APrime_eq_top_of_eq_OPrime [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : N = OPrime p G) :
    APrime p N = ⊤ := by
  classical
  let A : Subgroup N := APrime p N
  haveI hA_char : A.Characteristic := by
    simpa [A] using APrime_characteristic (p := p) (G := N)
  haveI hAmap_normal : (A.map N.subtype).Normal := inferInstance
  have hAmap_le_N : A.map N.subtype ≤ N :=
    Subgroup.map_subtype_le A
  obtain ⟨a, hN_index⟩ : ∃ a : ℕ, N.index = p ^ a := by
    rw [hN]
    exact OPrime_index_isPGroup p G
  obtain ⟨b, hA_index⟩ : ∃ b : ℕ, A.index = p ^ b := by
    simpa [A] using APrime_index_isPGroup p N
  have hAmap_index : (A.map N.subtype).index = p ^ (b + a) := by
    rw [Subgroup.index_map_subtype, hA_index, hN_index, ← pow_add]
  have hN_le_Amap : N ≤ A.map N.subtype := by
    have hO_le_Amap : OPrime p G ≤ A.map N.subtype :=
      OPrime_le hAmap_normal hAmap_index
    exact hN.symm ▸ hO_le_Amap
  have hAmap_eq_N : A.map N.subtype = N :=
    le_antisymm hAmap_le_N hN_le_Amap
  have hA_eq_top : A = ⊤ := by
    apply (Subgroup.map_subtype_inj (H := N)).mp
    rw [hAmap_eq_N, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simpa [A] using hA_eq_top

/-- "Sylow `p`-subgroup `P` controls its own G-fusion": for any two elements `x, y ∈ P`
that are conjugate in `G`, they are already conjugate by some element of `P`.

Isaacs §5C-§5E で頻出. mathlib 未収載のため新規定義. -/
def _root_.Sylow.ControlsOwnFusion {p : ℕ} {G : Type*} [Group G] (P : Sylow p G) : Prop :=
  (P : Subgroup G).ControlsFusionIn (P : Subgroup G)

/-- **Isaacs Thm 5.25 (⇒)**: G has normal p-complement ⇒ any Sylow_p `P` controls own fusion.

**証明** (Isaacs p.173): 与えられた N normal p-comp で `G = N · P`, `N ⊓ P = ⊥`.
x, y ∈ P G-conjugate: ∃ g, g x g⁻¹ = y. `mem_sup_of_normal_left` で `g = n · p`
(n ∈ N, p ∈ P). z := p x p⁻¹ ∈ P. `g x g⁻¹ = n z n⁻¹ = y ∈ P`. 一方
`n z n⁻¹ · z⁻¹ = n · (z n⁻¹ z⁻¹) ∈ N` (N normal) かつ `∈ P` (= y · z⁻¹). よって
`∈ N ⊓ P = ⊥`, つまり `n z n⁻¹ = z = p x p⁻¹ = y`. `u = p` で完了. -/
theorem controlsOwnFusion_of_hasNormalPComplement [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hG : HasNormalPComplement p G) :
    P.ControlsOwnFusion := by
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  haveI : N.Normal := hN_normal
  rintro x y hx_P hy_P ⟨g, hgxy⟩
  -- g ∈ N ⊔ P = ⊤ ⇒ g = n · p (n ∈ N, p ∈ P)
  have h_sup_top : N ⊔ (P : Subgroup G) = ⊤ := (hN_compl P).sup_eq_top
  have hg_in_sup : g ∈ N ⊔ (P : Subgroup G) := h_sup_top ▸ Subgroup.mem_top g
  obtain ⟨n, hn_N, q, hq_P, hg_eq⟩ := Subgroup.mem_sup_of_normal_left.mp hg_in_sup
  -- z := q * x * q⁻¹ ∈ P
  have hz_P : q * x * q⁻¹ ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hq_P hx_P)
      ((P : Subgroup G).inv_mem hq_P)
  -- y = g x g⁻¹ = n · (q x q⁻¹) · n⁻¹ = n z n⁻¹
  have h_y_eq : y = n * (q * x * q⁻¹) * n⁻¹ := by
    rw [← hgxy, ← hg_eq]; group
  -- n z n⁻¹ ∈ P (= y)
  have h_nzn_in_P : n * (q * x * q⁻¹) * n⁻¹ ∈ (P : Subgroup G) := h_y_eq ▸ hy_P
  -- n z n⁻¹ · z⁻¹ ∈ N: rewrite as n · (z n⁻¹ z⁻¹) with z n⁻¹ z⁻¹ ∈ N (conj)
  have h_in_N : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ N := by
    have hzn_inv_z_inv_N : (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ N :=
      hN_normal.conj_mem n⁻¹ (N.inv_mem hn_N) (q * x * q⁻¹)
    have heq : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ =
               n * ((q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹) := by group
    rw [heq]
    exact N.mul_mem hn_N hzn_inv_z_inv_N
  -- n z n⁻¹ · z⁻¹ ∈ P
  have h_in_P : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem h_nzn_in_P ((P : Subgroup G).inv_mem hz_P)
  -- n z n⁻¹ · z⁻¹ ∈ N ⊓ P = ⊥, so equal to 1
  have h_eq_one : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ = 1 := by
    have h_in_inf : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ N ⊓ (P : Subgroup G) :=
      ⟨h_in_N, h_in_P⟩
    rw [(hN_compl P).disjoint.eq_bot, Subgroup.mem_bot] at h_in_inf
    exact h_in_inf
  -- n z n⁻¹ = z, so y = z = q x q⁻¹
  rw [mul_inv_eq_one] at h_eq_one
  refine ⟨q, hq_P, ?_⟩
  rw [h_y_eq, h_eq_one]

/-- **Helper for Thm 5.25 (⇐)**: heart of the proof. Sylow_p `P` that controls its own G-fusion
satisfies `P ⊓ OPrime p G = ⊥`. The rest of Thm 5.25 (⇐) is a Sylow-conjugacy + cardinality
assembly on top of this.

**証明スケッチ** (Isaacs p.173):
* `N := OPrime p G`. `Q := (P ⊓ N).subgroupOf N` is Sylow `p` of `↥N` (cardinality argument:
  `|P ⊓ N| = |P| / [G : N · P]` and `N · P = G` from `[G:N]` being p-power dividing `|P|`).
* **APrime p ↥N = ⊤**: `APrime p ↥N` is characteristic in `↥N` (Aut(N) preserves the
  defining family) ⇒ its `.map N.subtype` is normal in `G`. It has p-power index in `G`
  (= `|G:N| · |↥N : APrime|`), so by `OPrime` minimality `N ≤ (APrime).map subtype ≤ N`,
  hence equality, hence `APrime p ↥N = ⊤` in `↥N`.
* **Focal Subgroup Theorem**: `APrime p ↥N = ⊤` and transfer-focal give
  `focalSubgroup Q = Q`. This is the `A^p(N)=N` line in Isaacs followed by Thm 5.21,
  without adding an extra public bridge through `commutator ↥N`.
* **ControlsOwnFusion lift**: every generator `⁅x, u⁆ ∈ focalSubgroup Q` (with `x ∈ Q`,
  `u ∈ ↥N` such that `[x,u] ∈ Q`) can be rewritten using ControlsOwnFusion. Set
  `y := u x u⁻¹ ∈ Q ⊆ P`; controlsOwnFusion gives `v ∈ P` with `v x v⁻¹ = y`. Then
  `[x, v⁻¹] = x⁻¹ y` is in `⁅Q.map N.subtype, (P : Subgroup G)⁆`. Hence
  `focalSubgroup Q ≤ ⁅Q.map subtype, P⁆` (viewing all in `G`).
* **Iteration**: Combine the previous two: `Q.map subtype ≤ ⁅Q.map subtype, P⁆` in `G`. By
  induction on `n`, `Q.map subtype ≤ lowerCentralSeries (P : Subgroup G) n`.
  (Base: `Q.map subtype ≤ P` since `Q ⊆ P`. Step: `Q.map subtype ≤ ⁅Q.map subtype, P⁆ ≤
  ⁅lowerCentralSeries P n, ⊤⁆ = lowerCentralSeries P (n+1)`.)
* **Termination**: `P` is a finite p-group ⇒ `IsNilpotent P` (`IsPGroup.isNilpotent`) ⇒
  `∃ n, lowerCentralSeries P n = ⊥` (`Subgroup.nilpotent_iff_lowerCentralSeries`). Hence
  `Q.map subtype = ⊥` in `G`, so `(P : Subgroup G) ⊓ N = ⊥`.

The proof below implements these steps directly. -/
lemma OPrime_meet_sylow_eq_bot_of_controlsOwnFusion [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : P.ControlsOwnFusion) :
    (P : Subgroup G) ⊓ OPrime p G = ⊥ := by
  set N : Subgroup G := OPrime p G with hN_def
  haveI hN_normal : N.Normal := inferInstance
  set R : Subgroup G := (P : Subgroup G) ⊓ N with hR_def
  have hR_le_P : R ≤ (P : Subgroup G) := by
    rw [hR_def]
    exact inf_le_left
  -- Controls-own-fusion converts focal generators of `R` into commutators with `P`.
  have h_focal_R_le_comm : R.focalSubgroup ≤ ⁅R, (P : Subgroup G)⁆ := by
    rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro g ⟨hgR, x, hxR, u, rfl⟩
    have hyR : u * x * u⁻¹ ∈ R := by
      have hy_eq : u * x * u⁻¹ = (⁅x, u⁆)⁻¹ * x := by
        rw [commutatorElement_def]
        group
      rw [hy_eq]
      exact R.mul_mem (R.inv_mem hgR) hxR
    obtain ⟨v, hvP, hv⟩ := hP (hR_le_P hxR) (hR_le_P hyR) ⟨u, rfl⟩
    have hcomm_eq : ⁅x, u⁆ = ⁅x, v⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc
        x * u * x⁻¹ * u⁻¹ = x * (u * x * u⁻¹)⁻¹ := by group
        _ = x * (v * x * v⁻¹)⁻¹ := by rw [hv]
        _ = x * v * x⁻¹ * v⁻¹ := by group
    rw [hcomm_eq]
    exact Subgroup.commutator_mem_commutator hxR hvP
  -- **Crux**: `R ≤ ⁅R, (P : Subgroup G)⁆`.
  -- 内訳: APrime ↥N = ⊤ (char + OPrime minimality) → transfer-focal で
  -- focalSubgroup Q = Q → 各 focal generator ⁅x, u⁆ (x ∈ Q, u ∈ ↥N) を
  -- ControlsOwnFusion で ⁅Q.map subtype, P⁆ 内 commutator に変換.
  have h_R_le_comm : R ≤ ⁅R, (P : Subgroup G)⁆ := by
    have h_R_le_focal : R ≤ R.focalSubgroup := by
      have hR_le_N : R ≤ N := by
        rw [hR_def]
        exact inf_le_right
      have hR_pgroup : IsPGroup p R :=
        P.isPGroup'.to_le hR_le_P
      have hRN_pgroup : IsPGroup p (R.subgroupOf N) :=
        hR_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hR_le_N).symm
      have hRN_not_dvd : ¬ p ∣ (R.subgroupOf N).index := by
        obtain ⟨a, hN_idx_pow⟩ : ∃ a : ℕ, N.index = p ^ a := by
          rw [hN_def]
          exact OPrime_index_isPGroup p G
        have hNP_coprime : Nat.Coprime N.index (P : Subgroup G).index := by
          rw [hN_idx_pow]
          exact (Nat.Prime.coprime_pow_of_not_dvd (m := a) Fact.out P.not_dvd_index).symm
        have hNP_top : N ⊔ (P : Subgroup G) = ⊤ :=
          OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index hNP_coprime
        have h_index_eq : (R.subgroupOf N).index = (P : Subgroup G).index := by
          have hR_le_N' : R ≤ N := hR_le_N
          have hR_rel_mul : R.relIndex N * N.index = R.index :=
            Subgroup.relIndex_mul_index hR_le_N'
          have hN_rel_P : N.relIndex (P : Subgroup G) = N.index := by
            rw [← Subgroup.relIndex_sup_right (H := (P : Subgroup G)) (K := N),
              sup_comm, hNP_top, Subgroup.relIndex_top_right]
          have hNP_rel_mul : N.relIndex (P : Subgroup G) * (P : Subgroup G).index =
              R.index := by
            have h := Subgroup.relIndex_inf_mul_relIndex (H := N)
              (K := (P : Subgroup G)) (L := (⊤ : Subgroup G))
            simpa [Subgroup.relIndex_top_right, hR_def, inf_comm] using h
          have hmul : R.relIndex N * N.index = (P : Subgroup G).index * N.index := by
            rw [hR_rel_mul, ← hNP_rel_mul, hN_rel_P, mul_comm N.index]
          have hrel : R.relIndex N = (P : Subgroup G).index :=
            Nat.eq_of_mul_eq_mul_right
              (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hmul
          exact hrel
        rw [h_index_eq]
        exact P.not_dvd_index
      let RN : Sylow p N := hRN_pgroup.toSylow hRN_not_dvd
      have hRN_eq : (RN : Subgroup N) = R.subgroupOf N :=
        hRN_pgroup.toSylow_coe hRN_not_dvd
      have hAPrime_top : APrime p N = ⊤ :=
        APrime_eq_top_of_eq_OPrime (G := G) (p := p) (N := N) hN_def
      have hRN_focal_eq : RN.focalSubgroup = (RN : Subgroup N) :=
        sylow_focalSubgroup_eq_self_of_APrime_eq_top RN hAPrime_top
      have hRN_le_focal : R.subgroupOf N ≤ RN.focalSubgroup := by
        intro x hx
        rw [hRN_focal_eq, hRN_eq]
        exact hx
      have hRN_focal_map_le : RN.focalSubgroup.map N.subtype ≤ R.focalSubgroup := by
        rw [Subgroup.focalSubgroup_def, MonoidHom.map_closure, Subgroup.focalSubgroup_def]
        apply Subgroup.closure_mono
        rintro y ⟨z, hz, rfl⟩
        rcases hz with ⟨hzRN, x, hxRN, u, rfl⟩
        have hzR : ((⁅x, u⁆ : N) : G) ∈ R := hzRN
        have hxR : (x : G) ∈ R := by
          have hxRN' : x ∈ R.subgroupOf N := by
            rwa [hRN_eq] at hxRN
          exact hxRN'
        exact ⟨hzR, (x : G), hxR, (u : G), rfl⟩
      intro r hr
      let x : N := ⟨r, hR_le_N hr⟩
      have hxRN : x ∈ R.subgroupOf N := hr
      have hxFocal : x ∈ RN.focalSubgroup := hRN_le_focal hxRN
      exact hRN_focal_map_le (Subgroup.mem_map_of_mem N.subtype hxFocal)
    exact h_R_le_focal.trans h_focal_R_le_comm
  -- Helper: `(⊤ : Subgroup ↥P).map P.subtype = P` (via `range_eq_map` + `range_subtype`).
  have h_top_map : ((⊤ : Subgroup ↥(P : Subgroup G))).map (P : Subgroup G).subtype =
      (P : Subgroup G) := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  -- **Step 5 (iteration)**: `∀ n, R ≤ ((⊤ : Subgroup ↥P).lowerCentralSeries n).map P.subtype`.
  -- Base: R ⊆ P = ⊤.map subtype. Step: R ≤ ⁅R, P⁆ = ⁅R, ⊤.map subtype⁆ ≤ ⁅(lcs n).map, ⊤.map⁆
  --       = (⁅lcs n, ⊤⁆).map = (lcs (n+1)).map.
  have h_R_le_lcs : ∀ n : ℕ, R ≤ Subgroup.map (P : Subgroup G).subtype
      ((⊤ : Subgroup ↥(P : Subgroup G)).lowerCentralSeries n) := by
    intro n
    induction n with
    | zero =>
      show R ≤ Subgroup.map (P : Subgroup G).subtype ⊤
      rw [h_top_map]
      exact inf_le_left
    | succ n ih =>
      change R ≤ Subgroup.map (P : Subgroup G).subtype
        ⁅(⊤ : Subgroup ↥(P : Subgroup G)).lowerCentralSeries n,
          (⊤ : Subgroup ↥(P : Subgroup G))⁆
      rw [Subgroup.map_commutator, h_top_map]
      exact h_R_le_comm.trans (Subgroup.commutator_mono ih le_rfl)
  -- **Step 6 (termination)**: `P` is a finite p-group ⇒ nilpotent ⇒ `∃ n, lcs ↥P n = ⊥`.
  haveI hP_pgroup : IsPGroup p ↥(P : Subgroup G) := P.isPGroup'
  haveI hP_nilp : Group.IsNilpotent ↥(P : Subgroup G) := hP_pgroup.isNilpotent
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hP_nilp
  have : R ≤ ⊥ := by
    have := h_R_le_lcs n
    rw [hn, Subgroup.map_bot] at this
    exact this
  exact le_bot_iff.mp this

/-- **Isaacs Thm 5.25 (⇐)**: any Sylow_p `P` controls own fusion ⇒ G has normal p-complement.

**証明** (Isaacs p.173, harder direction): `N := OPrime p G`. 主な仕事は
`(P : Subgroup G) ⊓ N = ⊥` を示すことで, これが
`OPrime_meet_sylow_eq_bot_of_controlsOwnFusion` (前置の helper). 残りは:
(B) Sylow II + N normal で任意 Sylow `R` に拡張 (`g • (P ⊓ N) = (g • P) ⊓ N`). ✅
(C) p ∤ |N| (任意 Sylow R で R ⊓ N = ⊥ + Cauchy 矛盾) → `|N| · |P'| = |G|` +
    `Nat.Coprime (|N|) (p^a)` → `Subgroup.isComplement'_of_coprime`. ✅

**実装状態 (2026-05-25)**: Step A (heart) + Steps B/C 完成 (sorry-free). -/
theorem hasNormalPComplement_of_controlsOwnFusion [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : P.ControlsOwnFusion) :
    HasNormalPComplement p G := by
  -- Set N := OPrime p G, the normal-p-complement witness.
  set N : Subgroup G := OPrime p G with hN_def
  haveI hN_normal : N.Normal := inferInstance
  -- |G : N| is a p-power, say p^a.
  obtain ⟨a, hN_idx_pow⟩ := OPrime_index_isPGroup p G
  -- **Step A** (heart, deferred to helper): `(P : Subgroup G) ⊓ N = ⊥`.
  have h_PN_bot : (P : Subgroup G) ⊓ N = ⊥ :=
    OPrime_meet_sylow_eq_bot_of_controlsOwnFusion P hP
  -- **Step B**: Conjugation propagates Step A to every Sylow `R` (Sylow II + N normal):
  -- ∃ g, g • P = R. Then `(R ⊓ N) = (g • P) ⊓ (g • N) = g • (P ⊓ N) = g • ⊥ = ⊥`.
  have h_all_sylow : ∀ R : Sylow p G, (R : Subgroup G) ⊓ N = ⊥ := fun R => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P R
    have h_R_eq : (R : Subgroup G) = MulAut.conj g • (P : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    have h_N_eq : MulAut.conj g • N = N := Subgroup.Normal.conj_smul_eq_self g N
    calc (R : Subgroup G) ⊓ N
        = MulAut.conj g • (P : Subgroup G) ⊓ N := by rw [h_R_eq]
      _ = MulAut.conj g • (P : Subgroup G) ⊓ MulAut.conj g • N := by rw [h_N_eq]
      _ = MulAut.conj g • ((P : Subgroup G) ⊓ N) := (Subgroup.smul_inf _ _ _).symm
      _ = MulAut.conj g • (⊥ : Subgroup G) := by rw [h_PN_bot]
      _ = ⊥ := Subgroup.smul_bot _
  -- **Step C**: `p ∤ |N|` (any p-element in N would lie in some Sylow R, hence in R ⊓ N = ⊥)
  -- ⇒ `|N| · p^c = |G|` where `c = (|G|).factorization p` ⇒ `c = a` ⇒ `|N| · |P'| = |G|`
  -- + disjoint ⇒ `IsComplement' N P'`.
  refine ⟨N, hN_normal, fun P' => ?_⟩
  have h_P'N_bot : (P' : Subgroup G) ⊓ N = ⊥ := h_all_sylow P'
  -- C.1: p ∤ |N|
  have h_p_ndvd_N : ¬ p ∣ Nat.card ↥N := by
    intro hp_dvd
    obtain ⟨x, hx_order⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hp_dvd
    have hx_ne : (x : ↥N) ≠ 1 := by
      intro h; rw [h, orderOf_one] at hx_order
      exact (Fact.out : p.Prime).one_lt.ne hx_order
    -- (x : G) has the same order p (Subgroup.orderOf_coe)
    have hx_order_G : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hx_order
    -- ⟨x.val⟩ as Subgroup G is a p-group (cyclic of order p)
    have hpg : IsPGroup p (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card ((Nat.card_zpowers (x : G)).trans hx_order_G |>.trans (pow_one p).symm)
    obtain ⟨Q, hQ_le⟩ := hpg.exists_le_sylow
    have hxQ : (x : G) ∈ (Q : Subgroup G) := hQ_le (Subgroup.mem_zpowers _)
    have hxN : (x : G) ∈ N := x.property
    have h_in : (x : G) ∈ (Q : Subgroup G) ⊓ N := ⟨hxQ, hxN⟩
    rw [h_all_sylow Q, Subgroup.mem_bot] at h_in
    exact hx_ne (Subtype.ext h_in)
  -- C.2: factorization of |G| at p = a
  have h_fact_a : (Nat.card G).factorization p = a := by
    have hN_card_mul : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
    have h_total : Nat.card G = Nat.card ↥N * p ^ a := by rw [← hN_card_mul, hN_idx_pow]
    rw [h_total, Nat.factorization_mul (Nat.card_pos (α := ↥N)).ne'
      (pow_pos (Fact.out : p.Prime).pos a).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h_p_ndvd_N,
      Nat.Prime.factorization_pow (Fact.out : p.Prime),
      Finsupp.single_apply]
    simp
  -- C.3: |P'| = p^a, hence |N| · |P'| = |G|
  have hP'_card : Nat.card ↥(P' : Subgroup G) = p ^ a := by
    rw [P'.card_eq_multiplicity, h_fact_a]
  have h_card_mul : Nat.card ↥N * Nat.card ↥(P' : Subgroup G) = Nat.card G := by
    rw [hP'_card, ← hN_idx_pow]; exact Subgroup.card_mul_index N
  -- C.4: Coprime |N| |P'|
  have h_coprime : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(P' : Subgroup G)) := by
    rw [hP'_card]
    exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h_p_ndvd_N).symm).pow_right a
  exact Subgroup.isComplement'_of_coprime h_card_mul h_coprime

/-- **Isaacs Thm 5.25**: G has normal p-complement ⇔ Sylow_p controls own fusion. -/
theorem hasNormalPComplement_iff_controlsOwnFusion [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    HasNormalPComplement p G ↔ P.ControlsOwnFusion :=
  ⟨controlsOwnFusion_of_hasNormalPComplement P, hasNormalPComplement_of_controlsOwnFusion P⟩

/-! **Isaacs Thm 5.26 Frobenius normal p-complement** (forward declaration; theorem 化は下記)
は (1) ⇔ (3) で記述. 詳細は Lem 5.27, Lem 5.28 完成後の theorem 化を参照. -/

/-- **Isaacs Lem 5.27 part 1 (1 ⇒ 2, strong form)**: G が normal p-complement を持つなら,
任意の subgroup `H ≤ G` も normal p-complement を持つ.

`H` の p-complement は `N.subgroupOf H = N ⊓ H` viewed inside `H` (witness).

**証明** (Isaacs p.174): `N` は `G` で normal なので `N.subgroupOf H` は `H` で normal
(`Normal.subgroupOf`). Cardinality:

* 任意 Sylow `P₀ : Sylow p G` で `IsComplement' N P₀` ⇒ `N.index = |P₀| = p^v_p(|G|)`,
  `|N|` coprime to `p` (Sylow `not_dvd_index` + `IsComplement'.index_eq_card`).
* `(N.subgroupOf H).index ∣ N.index` (`relIndex_dvd_index_of_normal`) ⇒ p-power.
* `|N.subgroupOf H| = |M.map H.subtype| = |N ⊓ H| ∣ |N|` ⇒ coprime to `p`.
* 任意 Sylow `Q : Sylow p ↥H` で `|Q| = p^v_p(|H|)` (`Sylow.card_eq_multiplicity`).
* Lagrange + `Nat.factorization_mul` で `v_p(|H|) = a` (M.index = p^a の指数).
  ⇒ `|Q| = p^a = M.index`, よって `|N.subgroupOf H| * |Q| = |H|` + Coprime.
* `Subgroup.isComplement'_of_coprime` 適用. -/
theorem hasNormalPComplement_of_subgroup [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : HasNormalPComplement p G) (H : Subgroup G) :
    HasNormalPComplement p ↥H := by
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  haveI : N.Normal := hN_normal
  refine ⟨N.subgroupOf H, hN_normal.subgroupOf H, fun Q => ?_⟩
  set M : Subgroup ↥H := N.subgroupOf H with hM_def
  -- Get any Sylow P₀ in G
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p G))
  -- |P₀| = p^v_p(|G|)
  have hP₀_card : Nat.card ↥(P₀ : Subgroup G) = p ^ (Nat.card G).factorization p :=
    P₀.card_eq_multiplicity
  -- N.index = |P₀|
  have hN_idx_eq_P₀ : N.index = Nat.card ↥(P₀ : Subgroup G) :=
    (hN_compl P₀).symm.index_eq_card
  -- ¬ p ∣ |N|
  have h_p_ndvd_N : ¬ p ∣ Nat.card ↥N := by
    rw [← (hN_compl P₀).index_eq_card]; exact P₀.not_dvd_index
  -- |M| ∣ |N|: M ≃ N ⊓ H ≤ N via H.subtype
  have hM_card_dvd_N : Nat.card ↥M ∣ Nat.card ↥N := by
    have h_inj : Function.Injective (H.subtype : ↥H → G) := Subtype.coe_injective
    have h_card_eq : Nat.card ↥M = Nat.card ↥(M.map H.subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective M H.subtype h_inj).toEquiv
    rw [h_card_eq, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  -- ¬ p ∣ |M|
  have h_p_ndvd_M : ¬ p ∣ Nat.card ↥M := fun h => h_p_ndvd_N (h.trans hM_card_dvd_N)
  -- M.index ∣ N.index (relIndex_dvd_index_of_normal)
  have hM_idx_dvd_Nidx : M.index ∣ N.index :=
    Subgroup.relIndex_dvd_index_of_normal N H
  -- M.index = p^a for some a ≤ v_p(|G|)
  obtain ⟨a, _, hM_idx_pow⟩ : ∃ a ≤ (Nat.card G).factorization p, M.index = p ^ a :=
    (Nat.dvd_prime_pow Fact.out).mp ((hN_idx_eq_P₀.trans hP₀_card) ▸ hM_idx_dvd_Nidx)
  -- |Q| = p^v_p(|H|)
  have hQ_card : Nat.card ↥(Q : Subgroup ↥H) = p ^ (Nat.card ↥H).factorization p :=
    Q.card_eq_multiplicity
  -- |H| = |M| * M.index (Lagrange)
  have hL_M : Nat.card ↥M * M.index = Nat.card ↥H := by
    rw [mul_comm]; exact M.index_mul_card
  -- v_p(|H|) = a (from |M| * p^a = |H|, |M| coprime to p ⇒ v_p(|M|) = 0)
  have h_va : (Nat.card ↥H).factorization p = a := by
    have h_card_eq : Nat.card ↥M * p ^ a = Nat.card ↥H := by
      rw [← hM_idx_pow]; exact hL_M
    have hp_pos : 0 < p := (Fact.out (p := p.Prime)).pos
    have hM_ne : Nat.card ↥M ≠ 0 := Nat.card_pos.ne'
    have hpa_ne : p ^ a ≠ 0 := pow_ne_zero a hp_pos.ne'
    rw [← h_card_eq, Nat.factorization_mul hM_ne hpa_ne, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd h_p_ndvd_M,
        Nat.factorization_pow_self Fact.out, zero_add]
  -- |Q| = M.index
  have hQ_card_eq : Nat.card ↥(Q : Subgroup ↥H) = M.index := by
    rw [hQ_card, h_va, ← hM_idx_pow]
  -- |M| * |Q| = |H|
  have h_mul_eq : Nat.card ↥M * Nat.card ↥(Q : Subgroup ↥H) = Nat.card ↥H := by
    rw [hQ_card_eq]; exact hL_M
  -- Coprime |M| |Q|: |M| coprime to p ⇒ Coprime |M| p ⇒ Coprime |M| p^a
  have h_coprime : Nat.Coprime (Nat.card ↥M) (Nat.card ↥(Q : Subgroup ↥H)) := by
    rw [hQ_card, h_va]
    exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h_p_ndvd_M).symm).pow_right a
  exact Subgroup.isComplement'_of_coprime h_mul_eq h_coprime

/-- `(C_G(X)).subgroupOf (N_G(X))` は `N_G(X)` で normal (kernel of `normalizerMonoidHom`).
mathlib `normalizerMonoidHom_ker` 経由で機械的に得られるが、typeclass resolution が
直接行かないので明示 instance 化. -/
instance centralizer_subgroupOf_normalizer_normal (X : Subgroup G) :
    ((Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))).Normal := by
  rw [← X.normalizerMonoidHom_ker]
  infer_instance

/-- **Isaacs Lem 5.27 part 2 (2 ⇒ 3)**: 仮定「∀ 非自明 p-subgroup `X` ⊆ `G`,
`N_G(X)` が normal p-complement を持つ」 ⇒ 任意 p-subgroup `X` で
`↥N_G(X) / (C_G(X)).subgroupOf N_G(X)` は p-group.

**証明** (Isaacs p.174):
* `X = ⊥` の場合: `centralizer (⊥ : Set G) = ⊤` (1 と全 g が可換) ⇒
  `subgroupOf normalizer = ⊤` ⇒ 商 ↥(normalizer ⊥) ⧸ ⊤ は Subsingleton ⇒ p-group.
* `X ≠ ⊥` の場合: 仮定で `normalizer X` の normal p-complement `K'` を得る.
  `X.subgroupOf (normalizer X)` (`X_n`) は normal (`normal_in_normalizer`),
  `K'` も normal. `K' ⊓ X_n = ⊥` (|K'| coprime to p, |X_n| = |X| p-power,
  `inf_eq_bot_of_coprime`).
  `[K', X_n] ≤ K' ⊓ X_n = ⊥` (`commutator_le_inf` with両 normal) ⇒
  `K' ≤ centralizer X_n` (`commutator_eq_bot_iff_le_centralizer`).
  座標 ↥(normalizer X) → G で `K' ≤ (centralizer X).subgroupOf (normalizer X)` (`C_n`).
  `↥(normalizer X) ⧸ K'` は p-group (Sylow Q complement), `↥(normalizer X) ⧸ C_n` は
  その quotient (`QuotientGroup.map (id) ... K'≤C_n`) ⇒ `IsPGroup.of_surjective` で p-group. -/
theorem isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
    [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup p X →
        HasNormalPComplement p ↥(Subgroup.normalizer (X : Set G)))
    (X : Subgroup G) (hXp : IsPGroup p X) :
    IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
      (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  -- 統一戦略: `C_n := (centralizer X).subgroupOf (normalizer X)` の `index` が `p` 乗
  -- であることを示し, `IsPGroup.of_card` を介して `↥N ⧸ C_n` が p-group であることを導く.
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN_def
  -- ∃ b, C_n.index = p^b を示せばよい
  suffices h_idx_pow : ∃ b, ((Subgroup.centralizer (X : Set G)).subgroupOf N).index = p ^ b by
    obtain ⟨b, hb⟩ := h_idx_pow
    refine IsPGroup.of_card (n := b) ?_
    rw [← Subgroup.index_eq_card]; exact hb
  -- 場合分け
  by_cases hX_bot : X = ⊥
  · -- X = ⊥: centralizer = ⊤ ⇒ subgroupOf = ⊤ ⇒ index = 1 = p^0
    refine ⟨0, ?_⟩
    rw [pow_zero]
    have hSubgroup_top : (Subgroup.centralizer (X : Set G)).subgroupOf N = ⊤ := by
      ext ⟨g, hg⟩
      refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro b hb
      subst hX_bot
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hb
      rw [hb, one_mul, mul_one]
    rw [hSubgroup_top, Subgroup.index_top]
  · -- X ≠ ⊥: hypothesis gives K' normal p-complement, K' ≤ C_n, C_n.index ∣ K'.index = p^a
    obtain ⟨K', hK'_normal, hK'_compl⟩ := h X hX_bot hXp
    haveI : K'.Normal := hK'_normal
    let X_n : Subgroup ↥N := X.subgroupOf N
    haveI hX_n_normal : X_n.Normal := by
      change (X.subgroupOf (Subgroup.normalizer (X : Set G))).Normal
      exact Subgroup.normal_in_normalizer
    -- Sylow Q in ↥N
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p ↥N))
    have hQ_compl : Subgroup.IsComplement' K' (Q : Subgroup ↥N) := hK'_compl Q
    -- ¬ p ∣ |K'| (Sylow not_dvd_index + IsComplement'.index_eq_card)
    have h_p_ndvd_K' : ¬ p ∣ Nat.card ↥K' := by
      rw [← hQ_compl.index_eq_card]; exact Q.not_dvd_index
    -- X_n p-group (|X_n| = |X|)
    have h_X_n_pg : IsPGroup p X_n := by
      have hX_le_N : X ≤ N := Subgroup.le_normalizer
      have h_card_eq : Nat.card ↥X_n = Nat.card ↥X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_N).toEquiv
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXp
      exact IsPGroup.of_card (h_card_eq.trans hk)
    -- K' ⊓ X_n = ⊥ (coprime cards)
    have h_inf_bot : K' ⊓ X_n = ⊥ := by
      refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
      obtain ⟨k, hX_n_card⟩ := IsPGroup.iff_card.mp h_X_n_pg
      rw [hX_n_card]
      exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h_p_ndvd_K').symm).pow_right k
    -- [K', X_n] = ⊥ (commutator_le_inf with K', X_n both normal)
    have h_comm_bot : ⁅K', X_n⁆ = ⊥ :=
      le_bot_iff.mp (h_inf_bot ▸ Subgroup.commutator_le_inf K' X_n)
    -- K' ≤ centralizer (X_n : Set ↥N)
    have h_K'_cent : K' ≤ Subgroup.centralizer (X_n : Set ↥N) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h_comm_bot
    -- K' ≤ (centralizer X).subgroupOf N
    have h_K'_le_C_n : K' ≤ (Subgroup.centralizer (X : Set G)).subgroupOf N := by
      intro k hk
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro x hxX
      have hxN : x ∈ N := Subgroup.le_normalizer hxX
      have hx_in_Xn : (⟨x, hxN⟩ : ↥N) ∈ X_n := by
        change (⟨x, hxN⟩ : ↥N) ∈ X.subgroupOf N
        rw [Subgroup.mem_subgroupOf]; exact hxX
      have hkx_eq : (⟨x, hxN⟩ : ↥N) * k = k * (⟨x, hxN⟩ : ↥N) :=
        Subgroup.mem_centralizer_iff.mp (h_K'_cent hk) ⟨x, hxN⟩ hx_in_Xn
      exact congrArg Subtype.val hkx_eq
    -- K'.index = |Q| (IsComplement'.symm.index_eq_card)
    have hK'_idx : K'.index = Nat.card ↥(Q : Subgroup ↥N) := hQ_compl.symm.index_eq_card
    -- K'.index = p^a (Q is p-group)
    obtain ⟨a, hKa⟩ : ∃ a, K'.index = p ^ a := by
      rw [hK'_idx]; exact IsPGroup.iff_card.mp Q.isPGroup'
    -- C_n.index ∣ K'.index (K' ≤ C_n)
    have hC_n_idx_dvd : ((Subgroup.centralizer (X : Set G)).subgroupOf N).index ∣ K'.index :=
      Subgroup.index_dvd_of_le h_K'_le_C_n
    -- C_n.index = p^b for some b ≤ a
    rcases (Nat.dvd_prime_pow Fact.out).mp (hKa ▸ hC_n_idx_dvd) with ⟨b, _, hb⟩
    exact ⟨b, hb⟩

/-- Criterion after Isaacs Thm 5.26: to check
`N_G(X) / C_G(X)` is a p-group, it suffices to show that every q-subgroup (`q ≠ p`)
normalizing a p-subgroup `X` centralizes it.

This is the formal version of the paragraph preceding Cor 5.29. -/
theorem isPGroup_normalizerQuotientCentralizer_of_prime_subgroups_centralize
    [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      ∀ {X Q : Subgroup G}, IsPGroup p X → IsPGroup q Q →
        Q ≤ Subgroup.normalizer (X : Set G) →
        Q ≤ Subgroup.centralizer (X : Set G))
    (X : Subgroup G) (hXp : IsPGroup p X) :
    IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
      (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN_def
  set C : Subgroup N := (Subgroup.centralizer (X : Set G)).subgroupOf N with hC_def
  suffices h_idx_pow : ∃ b, C.index = p ^ b by
    obtain ⟨b, hb⟩ := h_idx_pow
    refine IsPGroup.of_card (n := b) ?_
    rw [← Subgroup.index_eq_card]
    exact hb
  have hC_index_ne_zero : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨C.index.primeFactorsList.length, ?_⟩
  rw [← List.prod_replicate, ← List.eq_replicate_of_mem ?_,
    Nat.prod_primeFactorsList hC_index_ne_zero]
  intro q hq
  obtain ⟨hq_prime, hq_dvd_C_index⟩ := (Nat.mem_primeFactorsList hC_index_ne_zero).mp hq
  haveI : Fact q.Prime := ⟨hq_prime⟩
  by_contra hq_ne_p
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow q N))
  let Q : Subgroup G := (S : Subgroup N).map N.subtype
  have hQ_q : IsPGroup q Q := S.isPGroup'.map N.subtype
  have hQ_le_N : Q ≤ Subgroup.normalizer (X : Set G) := by
    simpa [Q, hN_def] using Subgroup.map_subtype_le (H := N) (S : Subgroup N)
  have hQ_le_CG : Q ≤ Subgroup.centralizer (X : Set G) :=
    h hq_ne_p hXp hQ_q hQ_le_N
  have hS_le_C : (S : Subgroup N) ≤ C := by
    intro s hs
    rw [hC_def, Subgroup.mem_subgroupOf]
    exact hQ_le_CG (Subgroup.mem_map_of_mem N.subtype hs)
  have hC_dvd_S_index : C.index ∣ (S : Subgroup N).index :=
    Subgroup.index_dvd_of_le hS_le_C
  exact S.not_dvd_index (hq_dvd_C_index.trans hC_dvd_S_index)

/-- **N = S · C 補題**: `S : Sylow p N`, `C ⊴ N` で `N/C` が p-group ⇒
`(S : Subgroup N) ⊔ C = ⊤`.

**証明**: `mk' C : N →* N/C` 全射. `S.mapSurjective mk' surj : Sylow p (N/C)`.
`N/C` は p-group なので任意 Sylow p = ⊤ (cardinality 一致). よって
`S.map (mk' C) = ⊤`. `comap_map_eq` で `S ⊔ ker (mk' C) = S ⊔ C = ⊤`. -/
private lemma sylow_sup_normal_eq_top_of_quot_isPGroup
    {N : Type*} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]
    {C : Subgroup N} [C.Normal] (hQ : IsPGroup p (N ⧸ C))
    (S : Sylow p N) :
    (S : Subgroup N) ⊔ C = ⊤ := by
  have hSurj : Function.Surjective (QuotientGroup.mk' C : N →* N ⧸ C) :=
    QuotientGroup.mk'_surjective C
  let S' : Sylow p (N ⧸ C) := S.mapSurjective hSurj
  -- (S' : Subgroup (N ⧸ C)) = ⊤ via cardinality
  have h_S'_top : (S' : Subgroup (N ⧸ C)) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [S'.card_eq_multiplicity]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    rw [hk, Nat.factorization_pow_self Fact.out]
  -- Translate back: S ⊔ C = ⊤
  have h_S_map : (S : Subgroup N).map (QuotientGroup.mk' C) = ⊤ := h_S'_top
  have h := Subgroup.comap_map_eq (f := QuotientGroup.mk' C) (S : Subgroup N)
  rw [h_S_map, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
  exact h.symm

/-- **"Normalizers grow" in p-group** (mathlib `lt_normalizer_of_isNilpotent_of_lt_top` の
p-group 特殊化). `G` finite p-group, `H : Subgroup G` で `H < ⊤` ⇒
`H < Subgroup.normalizer (H : Set G)`. -/
private lemma lt_normalizer_of_pgroup_of_lt_top
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) {H : Subgroup G} (hH : H < ⊤) :
    H < Subgroup.normalizer (H : Set G) := by
  haveI : Group.IsNilpotent G := IsPGroup.isNilpotent hG
  exact OddOrder.Isaacs.Ch01.lt_normalizer_of_isNilpotent_of_lt_top hH

/-- **Isaacs Lem 5.28**: 仮定「∀ p-subgroup `X` ⊆ `G`, `N_G(X)/C_G(X)` は p-group」
⇒ 任意 `P, Q : Sylow p G` で `Q = P^c` (= `c • Q = P` in mathlib 流) を満たす
`c ∈ C_G(P ⊓ Q)` が存在. **Frobenius normal p-complement 5.26 の鍵補題**.

**証明** (Isaacs p.174-175): `D := P ⊓ Q` の cardinality に関する強帰納法 (counter-example
の最大 `|D|` を取る). `D < P, D < Q` (else `P = Q`, `c = 1`).
* `N := N_G(D)`, `C := C_G(D)`, 仮定で `N/C` は p-group.
* `P ⊓ N = N_P(D) > D` (`IsPGroup.lt_normalizer_subgroupOf`).
* `S := Sylow p N ⊇ P ⊓ N`, `T := Sylow p N ⊇ Q ⊓ N`, `R := Sylow p G ⊇ S`.
* `N = S · C` (`sylow_sup_normal_eq_top_of_quot_isPGroup`).
* Sylow II in `N`: `T = n • S`, `n = s · y`, `s ∈ S`, `y ∈ C` ⇒ `T = y • S ⊆ y • R = R^y`.
* `P ⊓ R ⊇ P ⊓ N > D` ⇒ IH on `(P, R)`: `∃ x ∈ C_G(P ⊓ R), x • R = P`. `x` centralizes `D`.
* `R^y ⊓ Q ⊇ T ⊓ Q ⊇ Q ⊓ N > D` ⇒ IH on `(R^y, Q)`: `∃ z ∈ C_G(R^y ⊓ Q), z • Q = R^y`.
  `z` centralizes `D`.
* `(x y z) • Q = x • y • z • Q = x • (y • R^y) = x • R = P`. `x, y, z` all centralize `D`,
  hence `xyz ∈ C_G(D)`. 完了.

**実装状態 (2026-05-24)**: 助補題 (sylow_sup_normal + normalizers grow) は実装済.
本体は ~250 LOC で骨格のみ. 完全形式化は別 session.

**FT クリティカル**: Frobenius 5.26 (3⇒1) 経由. -/
theorem isaacs_lem_5_28 [Finite G] {p : ℕ} [Fact p.Prime]
    (hH : ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))))
    (P Q : Sylow p G) :
    ∃ c ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (Q : Subgroup G)) : Set G),
      c • Q = P := by
  -- Strong induction on `k = ((P : Subgroup G) ⊓ Q).index`. Smaller k = larger intersection.
  suffices h : ∀ k : ℕ, ∀ (P Q : Sylow p G),
      ((P : Subgroup G) ⊓ (Q : Subgroup G)).index = k →
      ∃ c ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (Q : Subgroup G)) : Set G),
        c • Q = P by exact h _ P Q rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P Q hk
    -- **Case 1**: P = Q. Take c = 1.
    by_cases hPQ : P = Q
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [hPQ, one_smul]
    -- **Case 2**: P ≠ Q. Apply textbook argument.
    · -- D := P ⊓ Q. P ≠ Q + Sylow card equality ⇒ D < P, D < Q.
      set D : Subgroup G := (P : Subgroup G) ⊓ (Q : Subgroup G) with hD_def
      have hPQ_card_eq : Nat.card ↥(P : Subgroup G) = Nat.card ↥(Q : Subgroup G) := by
        rw [P.card_eq_multiplicity, Q.card_eq_multiplicity]
      have hD_lt_P : D < (P : Subgroup G) := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h_eq
        have hP_le_Q : (P : Subgroup G) ≤ (Q : Subgroup G) := h_eq ▸ inf_le_right
        have h_subgroup_eq : (P : Subgroup G) = (Q : Subgroup G) :=
          Subgroup.eq_of_le_of_card_ge hP_le_Q hPQ_card_eq.symm.le
        exact hPQ (Sylow.ext h_subgroup_eq)
      have hD_lt_Q : D < (Q : Subgroup G) := by
        refine lt_of_le_of_ne inf_le_right ?_
        intro h_eq
        have hQ_le_P : (Q : Subgroup G) ≤ (P : Subgroup G) := h_eq ▸ inf_le_left
        have h_subgroup_eq : (P : Subgroup G) = (Q : Subgroup G) :=
          (Subgroup.eq_of_le_of_card_ge hQ_le_P hPQ_card_eq.le).symm
        exact hPQ (Sylow.ext h_subgroup_eq)
      -- N := normalizer D, C := centralizer D
      set N : Subgroup G := Subgroup.normalizer (D : Set G) with hN_def
      set C : Subgroup G := Subgroup.centralizer (D : Set G) with hC_def
      -- D ≤ N (le_normalizer), D ≤ P (already), D ≤ Q (already), D ≤ C (D centralizes itself? NO!)
      -- D centralizes itself only if D is abelian. Skip — we don't need D ≤ C.
      have hD_le_N : D ≤ N := Subgroup.le_normalizer
      have hD_le_P : D ≤ (P : Subgroup G) := inf_le_left
      have hD_le_Q : D ≤ (Q : Subgroup G) := inf_le_right
      -- D is p-group (subgroup of P p-group)
      have hD_pgroup : IsPGroup p ↥D := P.isPGroup'.to_le inf_le_left
      -- hH applied: ↥N ⧸ C.subgroupOf N is p-group
      have h_quot_pgroup : IsPGroup p (↥N ⧸ C.subgroupOf N) := hH D hD_pgroup
      -- **Step 1**: P ⊓ N > D via "normalizers grow" in ↥P
      have hPN_gt_D : D < (P : Subgroup G) ⊓ N := by
        have hD_sub_P_lt_top : D.subgroupOf (P : Subgroup G) < ⊤ := by
          rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
          intro h_le; exact (not_le_of_gt hD_lt_P) h_le
        have h_lt_norm : D.subgroupOf (P : Subgroup G) <
            Subgroup.normalizer ((D.subgroupOf (P : Subgroup G)) : Set ↥(P : Subgroup G)) :=
          lt_normalizer_of_pgroup_of_lt_top P.isPGroup' hD_sub_P_lt_top
        have h_norm_eq : Subgroup.normalizer ((D.subgroupOf (P : Subgroup G)) :
            Set ↥(P : Subgroup G)) = N.subgroupOf (P : Subgroup G) :=
          (Subgroup.subgroupOf_normalizer_eq hD_le_P).symm
        rw [h_norm_eq] at h_lt_norm
        -- D.subgroupOf P < N.subgroupOf P (in ↥P). |·| translates to G.
        have h_card_lt : Nat.card ↥(D.subgroupOf (P : Subgroup G)) <
            Nat.card ↥(N.subgroupOf (P : Subgroup G)) := by
          have h_dvd := Subgroup.card_dvd_of_le h_lt_norm.le
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos h_dvd) ?_
          intro hcardeq
          exact h_lt_norm.ne
            (Subgroup.eq_of_le_of_card_ge h_lt_norm.le hcardeq.symm.le)
        have h_card_D : Nat.card ↥(D.subgroupOf (P : Subgroup G)) = Nat.card ↥D :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le_P).toEquiv
        have h_card_NP : Nat.card ↥(N.subgroupOf (P : Subgroup G)) =
            Nat.card ↥((P : Subgroup G) ⊓ N) := by
          rw [show (P : Subgroup G) ⊓ N = N ⊓ (P : Subgroup G) from inf_comm _ _,
              ← Subgroup.subgroupOf_map_subtype]
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective _ _ ((P : Subgroup G).subtype_injective)).toEquiv
        rw [h_card_D, h_card_NP] at h_card_lt
        exact lt_of_le_of_ne (le_inf hD_le_P hD_le_N)
          (fun h => Nat.lt_irrefl _ (h ▸ h_card_lt))
      -- **Step 2**: Q ⊓ N > D (symmetric)
      have hQN_gt_D : D < (Q : Subgroup G) ⊓ N := by
        have hD_sub_Q_lt_top : D.subgroupOf (Q : Subgroup G) < ⊤ := by
          rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
          intro h_le; exact (not_le_of_gt hD_lt_Q) h_le
        have h_lt_norm : D.subgroupOf (Q : Subgroup G) <
            Subgroup.normalizer ((D.subgroupOf (Q : Subgroup G)) : Set ↥(Q : Subgroup G)) :=
          lt_normalizer_of_pgroup_of_lt_top Q.isPGroup' hD_sub_Q_lt_top
        have h_norm_eq : Subgroup.normalizer ((D.subgroupOf (Q : Subgroup G)) :
            Set ↥(Q : Subgroup G)) = N.subgroupOf (Q : Subgroup G) :=
          (Subgroup.subgroupOf_normalizer_eq hD_le_Q).symm
        rw [h_norm_eq] at h_lt_norm
        have h_card_lt : Nat.card ↥(D.subgroupOf (Q : Subgroup G)) <
            Nat.card ↥(N.subgroupOf (Q : Subgroup G)) := by
          have h_dvd := Subgroup.card_dvd_of_le h_lt_norm.le
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos h_dvd) ?_
          intro hcardeq
          exact h_lt_norm.ne
            (Subgroup.eq_of_le_of_card_ge h_lt_norm.le hcardeq.symm.le)
        have h_card_D : Nat.card ↥(D.subgroupOf (Q : Subgroup G)) = Nat.card ↥D :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le_Q).toEquiv
        have h_card_NQ : Nat.card ↥(N.subgroupOf (Q : Subgroup G)) =
            Nat.card ↥((Q : Subgroup G) ⊓ N) := by
          rw [show (Q : Subgroup G) ⊓ N = N ⊓ (Q : Subgroup G) from inf_comm _ _,
              ← Subgroup.subgroupOf_map_subtype]
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective _ _ ((Q : Subgroup G).subtype_injective)).toEquiv
        rw [h_card_D, h_card_NQ] at h_card_lt
        exact lt_of_le_of_ne (le_inf hD_le_Q hD_le_N)
          (fun h => Nat.lt_irrefl _ (h ▸ h_card_lt))
      -- **Step 3**: Sylow p of ↥N containing (P ⊓ N).subgroupOf N, (Q ⊓ N).subgroupOf N
      have hPN_pgroup_in_N : IsPGroup p ↥(((P : Subgroup G) ⊓ N).subgroupOf N) := by
        have h_iso : ((P : Subgroup G) ⊓ N).subgroupOf N ≃* ↥((P : Subgroup G) ⊓ N) :=
          Subgroup.subgroupOfEquivOfLe inf_le_right
        exact (P.isPGroup'.to_le inf_le_left).of_equiv h_iso.symm
      have hQN_pgroup_in_N : IsPGroup p ↥(((Q : Subgroup G) ⊓ N).subgroupOf N) := by
        have h_iso : ((Q : Subgroup G) ⊓ N).subgroupOf N ≃* ↥((Q : Subgroup G) ⊓ N) :=
          Subgroup.subgroupOfEquivOfLe inf_le_right
        exact (Q.isPGroup'.to_le inf_le_left).of_equiv h_iso.symm
      obtain ⟨S, hPN_le_S⟩ := IsPGroup.exists_le_sylow hPN_pgroup_in_N
      obtain ⟨T, hQN_le_T⟩ := IsPGroup.exists_le_sylow hQN_pgroup_in_N
      -- **Step 4**: R : Sylow p G containing S.map N.subtype
      set S_in_G : Subgroup G := (S : Subgroup ↥N).map N.subtype with hS_in_G_def
      have hS_in_G_pgroup : IsPGroup p ↥S_in_G := S.isPGroup'.map _
      obtain ⟨R, hS_in_G_le_R⟩ := IsPGroup.exists_le_sylow hS_in_G_pgroup
      -- **Step 5**: S ⊔ C.subgroupOf N = ⊤ in ↥N (via helper)
      have hS_sup_C : (S : Subgroup ↥N) ⊔ C.subgroupOf N = ⊤ :=
        sylow_sup_normal_eq_top_of_quot_isPGroup h_quot_pgroup S
      -- **Step 6**: Sylow II in ↥N: ∃ n : ↥N, n • S = T
      obtain ⟨n, hn_smul⟩ := MulAction.exists_smul_eq (↥N) S T
      -- **Step 7**: Decompose n = yC * sS (yC ∈ C.subgroupOf N, sS ∈ S)
      have hC_sup_S : C.subgroupOf N ⊔ (S : Subgroup ↥N) = ⊤ := by
        rw [sup_comm]; exact hS_sup_C
      have hn_in_top : (n : ↥N) ∈ C.subgroupOf N ⊔ (S : Subgroup ↥N) := by
        rw [hC_sup_S]; exact Subgroup.mem_top _
      obtain ⟨yC, hyC_in, sS, hsS_in, hn_eq⟩ := Subgroup.mem_sup_of_normal_left.mp hn_in_top
      -- **Step 8**: T = yC • S (since (yC * sS) • S = yC • (sS • S) = yC • S)
      have h_sS_S : (sS : ↥N) • S = S := by
        rw [Sylow.smul_eq_iff_mem_normalizer]; exact Subgroup.le_normalizer hsS_in
      have h_T_eq : T = yC • S := by
        rw [← hn_smul, ← hn_eq, mul_smul, h_sS_S]
      -- **Step 10 preview**: index strict inequality for IH (works for any subgroup > D).
      -- P ⊓ R ≥ P ⊓ N (via S_in_G ≤ R and P ⊓ N ⊆ S_in_G), and P ⊓ N > D.
      have hPN_le_S_in_G : (P : Subgroup G) ⊓ N ≤ S_in_G := by
        intro x hx
        have ⟨_, hx_N⟩ := Subgroup.mem_inf.mp hx
        refine ⟨⟨x, hx_N⟩, ?_, rfl⟩
        exact hPN_le_S (by rw [Subgroup.mem_subgroupOf]; exact hx)
      have hPN_le_R : (P : Subgroup G) ⊓ N ≤ (R : Subgroup G) :=
        hPN_le_S_in_G.trans hS_in_G_le_R
      have hPR_gt_D : D < (P : Subgroup G) ⊓ R :=
        lt_of_lt_of_le hPN_gt_D (le_inf inf_le_left hPN_le_R)
      -- **Step 9**: yR := yC.val • R (Sylow in G). Q ⊓ N ≤ yR.
      set yR : Sylow p G := (yC : G) • R with hyR_def
      have hQN_le_yR : (Q : Subgroup G) ⊓ N ≤ (yR : Subgroup G) := by
        intro q hq
        obtain ⟨hq_Q, hq_N⟩ := Subgroup.mem_inf.mp hq
        let q_N : ↥N := ⟨q, hq_N⟩
        have hq_N_in_QN : q_N ∈ ((Q : Subgroup G) ⊓ N).subgroupOf N := by
          rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_inf.mpr ⟨hq_Q, hq_N⟩
        have hq_N_in_T : q_N ∈ (T : Subgroup ↥N) := hQN_le_T hq_N_in_QN
        have hq_in_yCS : q_N ∈ ((yC • S : Sylow p ↥N) : Subgroup ↥N) := by
          rw [← h_T_eq]; exact hq_N_in_T
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq_in_yCS
        -- hq_in_yCS : (MulAut.conj yC)⁻¹ • q_N ∈ S
        have hs_in_R : ((MulAut.conj yC)⁻¹ q_N : ↥N).val ∈ (R : Subgroup G) := by
          apply hS_in_G_le_R
          exact ⟨(MulAut.conj yC)⁻¹ q_N, hq_in_yCS, rfl⟩
        show q ∈ (((yC : G) • R : Sylow p G) : Subgroup G)
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        -- Goal: (MulAut.conj (yC : G))⁻¹ q ∈ (R : Subgroup G)
        -- Both sides equal (yC : G)⁻¹ * q * (yC : G); ((MulAut.conj yC)⁻¹ q_N).val computes same
        convert hs_in_R using 1
        simp only [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.coe_mul,
          InvMemClass.coe_inv]
        rfl
      -- **Step 10**: index strict inequalities for IH (P, R) and (yR, Q)
      have hQyR_gt_D : D < (Q : Subgroup G) ⊓ yR :=
        lt_of_lt_of_le hQN_gt_D (le_inf inf_le_left hQN_le_yR)
      -- (P ⊓ R).index < k (D.index)
      have h_PR_idx_lt : ((P : Subgroup G) ⊓ R : Subgroup G).index < k := by
        rw [← hk]
        have h_dvd : ((P : Subgroup G) ⊓ R).index ∣ D.index :=
          Subgroup.index_dvd_of_le hPR_gt_D.le
        have h_D_idx_pos : 0 < D.index :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        refine lt_of_le_of_ne (Nat.le_of_dvd h_D_idx_pos h_dvd) ?_
        intro h_eq
        have h_card_eq : Nat.card ↥D = Nat.card ↥((P : Subgroup G) ⊓ R) := by
          have h1 := Subgroup.index_mul_card D
          have h2 := Subgroup.index_mul_card ((P : Subgroup G) ⊓ R)
          rw [h_eq] at h2
          exact Nat.eq_of_mul_eq_mul_left h_D_idx_pos (h1.trans h2.symm)
        exact hPR_gt_D.ne (Subgroup.eq_of_le_of_card_ge hPR_gt_D.le h_card_eq.ge)
      -- ((Q ⊓ yR)).index < k. Note inf_comm: Q ⊓ yR = yR ⊓ Q? Use Q ⊓ yR for symmetric IH.
      have h_QyR_idx_lt : ((Q : Subgroup G) ⊓ yR : Subgroup G).index < k := by
        rw [← hk]
        have h_dvd : ((Q : Subgroup G) ⊓ yR).index ∣ D.index :=
          Subgroup.index_dvd_of_le hQyR_gt_D.le
        have h_D_idx_pos : 0 < D.index :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        refine lt_of_le_of_ne (Nat.le_of_dvd h_D_idx_pos h_dvd) ?_
        intro h_eq
        have h_card_eq : Nat.card ↥D = Nat.card ↥((Q : Subgroup G) ⊓ yR) := by
          have h1 := Subgroup.index_mul_card D
          have h2 := Subgroup.index_mul_card ((Q : Subgroup G) ⊓ yR)
          rw [h_eq] at h2
          exact Nat.eq_of_mul_eq_mul_left h_D_idx_pos (h1.trans h2.symm)
        exact hQyR_gt_D.ne (Subgroup.eq_of_le_of_card_ge hQyR_gt_D.le h_card_eq.ge)
      -- **Step 11**: IH applications + combine c = x · yC.val⁻¹ · z
      -- IH on (P, R): (P : Subgroup G) ⊓ R as intersection (need to match shape)
      -- The IH wants ∃ c ∈ centralizer((P' ⊓ Q' : Set G)), c • Q' = P' for any P' Q' pair with
      -- index of P' ⊓ Q' < k. Apply to (P, R) and (yR, Q).
      obtain ⟨x, hx_C, hxR⟩ := ih _ h_PR_idx_lt P R rfl
      -- hx_C : x ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (R : Subgroup G)) : Set G)
      -- hxR : x • R = P
      -- For (yR, Q): index = (yR : Subgroup G) ⊓ Q. Hmm I have Q ⊓ yR.
      have hyRQ_inf_eq : (yR : Subgroup G) ⊓ Q = (Q : Subgroup G) ⊓ yR := inf_comm _ _
      have h_yRQ_idx_lt' : ((yR : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G).index < k := by
        rw [hyRQ_inf_eq]; exact h_QyR_idx_lt
      obtain ⟨z, hz_C, hzQ⟩ := ih _ h_yRQ_idx_lt' yR Q rfl
      -- hz_C : z ∈ Subgroup.centralizer (((yR : Subgroup G) ⊓ (Q : Subgroup G)) : Set G)
      -- hzQ : z • Q = yR
      -- c := x * yC.val⁻¹ * z
      refine ⟨x * (yC : G)⁻¹ * z, ?_, ?_⟩
      · -- c ∈ centralizer D
        have hyC_cent_D : (yC : G) ∈ Subgroup.centralizer (D : Set G) := by
          have : yC.val ∈ C := by
            have := hyC_in
            rwa [Subgroup.mem_subgroupOf] at this
          exact this
        have hyC_inv_cent_D : ((yC : G))⁻¹ ∈ Subgroup.centralizer (D : Set G) :=
          (Subgroup.centralizer (D : Set G)).inv_mem hyC_cent_D
        have hx_cent_D : x ∈ Subgroup.centralizer (D : Set G) := by
          have h_D_le : (D : Set G) ⊆ (((P : Subgroup G) ⊓ R : Subgroup G) : Set G) := by
            intro a ha
            exact Subgroup.mem_inf.mpr
              ⟨hD_le_P ha, hPN_le_R (le_inf hD_le_P hD_le_N ha)⟩
          exact Subgroup.centralizer_le h_D_le hx_C
        have hz_cent_D : z ∈ Subgroup.centralizer (D : Set G) := by
          have h_D_le : (D : Set G) ⊆ (((yR : Subgroup G) ⊓ Q : Subgroup G) : Set G) := by
            intro a ha
            refine Subgroup.mem_inf.mpr ⟨?_, hD_le_Q ha⟩
            -- a ∈ yR = yC.val • R; yC centralizes D so yC⁻¹ a yC = a ∈ R
            show a ∈ (((yC : G) • R : Sylow p G) : Subgroup G)
            rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
            have h_a_in_R : a ∈ (R : Subgroup G) :=
              hPN_le_R (le_inf hD_le_P hD_le_N ha)
            have h_comm : a * (yC : G) = (yC : G) * a :=
              Subgroup.mem_centralizer_iff.mp hyC_cent_D a ha
            have h_smul_eq : (MulAut.conj (yC : G))⁻¹ • a = a := by
              show (yC : G)⁻¹ * a * (yC : G) = a
              rw [mul_assoc, h_comm, ← mul_assoc, inv_mul_cancel, one_mul]
            rw [h_smul_eq]; exact h_a_in_R
          exact Subgroup.centralizer_le h_D_le hz_C
        exact (Subgroup.centralizer (D : Set G)).mul_mem
          ((Subgroup.centralizer (D : Set G)).mul_mem hx_cent_D hyC_inv_cent_D)
          hz_cent_D
      · -- c • Q = P
        -- z • Q = yR = yC.val • R, so yC.val⁻¹ • (z • Q) = R, (yC.val⁻¹ * z) • Q = R
        -- x • R = P, so x • ((yC.val⁻¹ * z) • Q) = P, (x * yC.val⁻¹ * z) • Q = P
        rw [show (x * (yC : G)⁻¹ * z) • Q = x • ((yC : G)⁻¹ • (z • Q)) by
          rw [← mul_smul, ← mul_smul]]
        rw [hzQ, hyR_def]
        rw [show ((yC : G)⁻¹ • (yC : G) • R : Sylow p G) = R from by
          rw [← mul_smul, inv_mul_cancel, one_smul]]
        exact hxR

/-- **Isaacs Thm 5.26 Frobenius normal p-complement** ⭐ **FT クリティカル**.
`G` has normal p-complement ⇔ ∀ p-subgroup `X`, `N_G(X)/C_G(X)` is p-group.

**証明** (Isaacs p.175-177):
* (1) ⇒ (3): `hasNormalPComplement_of_subgroup` (Lem 5.27 Part 1) で
  ∀ p-subgroup X non-trivial, `normalizer X` も normal p-comp を持つ.
  `isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement`
  (Lem 5.27 Part 2) で結論. ✅
* (3) ⇒ (1): 任意 Sylow `P` で `P.ControlsOwnFusion` を示し (Lem 5.28 経由),
  `hasNormalPComplement_of_controlsOwnFusion` (Thm 5.25 ⇐) で normal p-comp. ✅ -/
theorem hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer
    [Finite G] {p : ℕ} [Fact p.Prime] :
    HasNormalPComplement p G ↔
    ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  refine ⟨fun hG X hXp => ?_, fun hH => ?_⟩
  · -- (1) ⇒ (3): via Lem 5.27 Part 1 + Part 2 (both sorry-free)
    exact isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
      (fun Y _hY_ne _hY_pg => hasNormalPComplement_of_subgroup hG
        (Subgroup.normalizer (Y : Set G)))
      X hXp
  · -- (3) ⇒ (1): Pick Sylow P, show P.ControlsOwnFusion via Lem 5.28,
    -- then apply Thm 5.25 (⇐).
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
    refine (hasNormalPComplement_iff_controlsOwnFusion P).mpr ?_
    intro x y hx_P hy_P ⟨g, hgxy⟩
    -- Apply Lem 5.28 to (P, g • P)
    set gP : Sylow p G := g • P with hgP_def
    -- y ∈ P ⊓ gP
    have hy_in_gP : y ∈ (gP : Subgroup G) := by
      show y ∈ ((g • P : Sylow p G) : Subgroup G)
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have h_smul_eq : (MulAut.conj g)⁻¹ • y = x := by
        show g⁻¹ * y * g = x
        rw [← hgxy]; group
      rw [h_smul_eq]; exact hx_P
    have hy_in_PgP : y ∈ (P : Subgroup G) ⊓ (gP : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨hy_P, hy_in_gP⟩
    -- Lem 5.28: ∃ c ∈ C(P ⊓ gP), c • gP = P
    obtain ⟨c, hc_C, hc_smul⟩ := isaacs_lem_5_28 hH P gP
    -- c centralizes y
    have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.mp hc_C y hy_in_PgP).symm
    -- cg ∈ N(P): c • gP = P ⇒ (c * g) • P = P ⇒ cg ∈ normalizer
    have hcg_in_N : c * g ∈ Subgroup.normalizer (P : Set G) := by
      rw [← Sylow.smul_eq_iff_mem_normalizer, mul_smul, ← hgP_def]
      exact hc_smul
    set N_P : Subgroup G := Subgroup.normalizer (P : Set G) with hN_P_def
    -- P ≤ N(P) (general)
    have hP_le_N : (P : Subgroup G) ≤ N_P := Subgroup.le_normalizer
    -- P as Sylow of ↥N(P)
    let P_NP : Sylow p ↥N_P := P.subtype hP_le_N
    -- hH applied to P: ↥N(P) / C(P).subgroupOf N(P) is p-group
    have h_quot_pgroup : IsPGroup p
        (↥N_P ⧸ (Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P) :=
      hH P P.isPGroup'
    -- Normal instance for the centralizer subgroupOf
    haveI : ((Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P).Normal :=
      centralizer_subgroupOf_normalizer_normal (P : Subgroup G)
    -- N(P) = C(P).subgroupOf N(P) ⊔ P_NP (via helper applied to ↥N(P))
    have hSC_top : (P_NP : Subgroup ↥N_P) ⊔
        (Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P = ⊤ :=
      sylow_sup_normal_eq_top_of_quot_isPGroup h_quot_pgroup P_NP
    -- cg lifted to ↥N(P)
    let cg_N : ↥N_P := ⟨c * g, hcg_in_N⟩
    have hcg_in_sup : cg_N ∈ (Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P
        ⊔ (P_NP : Subgroup ↥N_P) := by
      rw [sup_comm]; rw [hSC_top]; exact Subgroup.mem_top _
    obtain ⟨t_N, ht_C, u_N, hu_P, htu_eq⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hcg_in_sup
    -- t_N : ↥N(P), t_N ∈ centralizer.subgroupOf ⇒ t_N.val ∈ centralizer P
    -- u_N : ↥N(P), u_N ∈ P_NP ⇒ u_N.val ∈ P
    have ht_in_C : (t_N : G) ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
      have := ht_C
      rwa [Subgroup.mem_subgroupOf] at this
    have hu_in_P : (u_N : G) ∈ (P : Subgroup G) := by
      have := hu_P
      change (u_N : G) ∈ (P : Subgroup G) at this ⊢
      exact this
    -- (cg).val = t_N.val * u_N.val
    have hcg_val_eq : c * g = (t_N : G) * (u_N : G) := by
      have h := congrArg Subtype.val htu_eq
      exact h.symm
    -- y = (cg) • x = (t_N.val * u_N.val) • x = t_N.val • (u_N.val • x) = u_N.val • x (t centralizes uxu⁻¹ ∈ P)
    refine ⟨(u_N : G), hu_in_P, ?_⟩
    -- Goal: u_N.val * x * u_N.val⁻¹ = y
    -- First: y = (cg) x (cg)⁻¹. From c * y = y * c, y = c y c⁻¹ = c (g x g⁻¹) c⁻¹ = (cg) x (cg)⁻¹.
    have h_y_eq_cgx : y = (c * g) * x * (c * g)⁻¹ := by
      have h_c_y_eq : c * y * c⁻¹ = y := by
        rw [hcy]; group
      calc y = c * y * c⁻¹ := h_c_y_eq.symm
        _ = c * (g * x * g⁻¹) * c⁻¹ := by rw [hgxy]
        _ = (c * g) * x * (c * g)⁻¹ := by group
    -- (cg) x (cg)⁻¹ = (t * u) x (t * u)⁻¹. Use t centralizes uxu⁻¹ ∈ P to simplify.
    have h_uux_in_P : (u_N : G) * x * (u_N : G)⁻¹ ∈ (P : Subgroup G) :=
      (P : Subgroup G).mul_mem
        ((P : Subgroup G).mul_mem hu_in_P hx_P)
        ((P : Subgroup G).inv_mem hu_in_P)
    have h_t_comm : ((u_N : G) * x * (u_N : G)⁻¹) * (t_N : G) =
        (t_N : G) * ((u_N : G) * x * (u_N : G)⁻¹) :=
      Subgroup.mem_centralizer_iff.mp ht_in_C _ h_uux_in_P
    have h_t_uxu_eq : (t_N : G) * ((u_N : G) * x * (u_N : G)⁻¹) * (t_N : G)⁻¹ =
        (u_N : G) * x * (u_N : G)⁻¹ := by
      rw [← h_t_comm]; group
    calc (u_N : G) * x * (u_N : G)⁻¹
        = (t_N : G) * ((u_N : G) * x * (u_N : G)⁻¹) * (t_N : G)⁻¹ := h_t_uxu_eq.symm
      _ = ((t_N : G) * (u_N : G)) * x * ((t_N : G) * (u_N : G))⁻¹ := by group
      _ = (c * g) * x * (c * g)⁻¹ := by rw [← hcg_val_eq]
      _ = y := h_y_eq_cgx.symm

/-- Isaacs' p-local action criterion, packaged with Frobenius' normal p-complement theorem.

If every q-subgroup (`q ≠ p`) normalizing a p-subgroup centralizes it, then `G` has a
normal p-complement. This is the shared entry point for Cor 5.29 and Cor 5.30. -/
theorem hasNormalPComplement_of_prime_subgroups_centralize
    [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      ∀ {X Q : Subgroup G}, IsPGroup p X → IsPGroup q Q →
        Q ≤ Subgroup.normalizer (X : Set G) →
        Q ≤ Subgroup.centralizer (X : Set G)) :
    HasNormalPComplement p G :=
  hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer.mpr
    (fun X hXp =>
      isPGroup_normalizerQuotientCentralizer_of_prime_subgroups_centralize h X hXp)

/-- If a q-group acts on a finite set, then `q` divides the number of non-fixed points. -/
private lemma prime_dvd_card_sub_card_fixedPoints_of_pgroup_action
    {A X : Type*} [Group A] [Group X] [Finite X] [MulDistribMulAction A X]
    {q : ℕ} [Fact q.Prime] (hA : IsPGroup q A) :
    q ∣ Nat.card X - Nat.card (MulAction.fixedPoints A X) := by
  have hmod := hA.card_modEq_card_fixedPoints X
  have hle : Nat.card (MulAction.fixedPoints A X) ≤ Nat.card X :=
    Nat.card_le_card_of_injective _ (fun _ _ h => Subtype.ext h)
  exact (Nat.modEq_iff_dvd' hle).mp hmod.symm

/-- Orbit-count step in Isaacs Cor 5.29.

If a q-group acts nontrivially by automorphisms on a finite p-group `X`, and `|X| = p^k`
with `k ≤ a`, then `q ∣ p^e - 1` for some `1 ≤ e ≤ a`. -/
private lemma exists_prime_dvd_pow_sub_one_of_nontrivial_pgroup_action
    {A X : Type*} [Group A] [Group X] [Finite X] [MulDistribMulAction A X]
    {p q a : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hX : IsPGroup p X) (hA : IsPGroup q A) (hpq : q ≠ p)
    (hX_bound : ∃ k, k ≤ a ∧ Nat.card X = p ^ k)
    (hfix_ne : MulAction.fixedPoints A X ≠ Set.univ) :
    ∃ e, 1 ≤ e ∧ e ≤ a ∧ q ∣ p ^ e - 1 := by
  classical
  let F : Subgroup X := {
    carrier := MulAction.fixedPoints A X
    one_mem' := by intro g; exact smul_one g
    mul_mem' := by
      intro x y hx hy g
      rw [smul_mul', hx g, hy g]
    inv_mem' := by
      intro x hx g
      rw [smul_inv', hx g] }
  have hF_card_lt : Nat.card F < Nat.card X := by
    change Nat.card (MulAction.fixedPoints A X) < Nat.card X
    simpa [Nat.card_coe_set_eq] using Set.ncard_lt_card hfix_ne
  have hF_index_ne_one : F.index ≠ 1 := by
    intro hidx_one
    have hidx := F.index_mul_card
    rw [hidx_one, one_mul] at hidx
    exact (Nat.lt_irrefl _ (hidx ▸ hF_card_lt))
  obtain ⟨e, he_index⟩ := hX.index F
  have he_pos : 1 ≤ e := by
    cases e with
    | zero =>
        exfalso
        exact hF_index_ne_one (by simpa using he_index)
    | succ e => exact Nat.succ_le_succ (Nat.zero_le e)
  obtain ⟨k, hk_le_a, hX_card⟩ := hX_bound
  have hF_index_dvd_card : F.index ∣ Nat.card X := by
    exact ⟨Nat.card F, F.index_mul_card.symm⟩
  have he_le_k : e ≤ k := by
    have hpow_dvd : p ^ e ∣ p ^ k := by
      rw [← he_index, ← hX_card]
      exact hF_index_dvd_card
    exact (pow_dvd_pow_iff (Fact.out : p.Prime).ne_zero
      (mt Nat.isUnit_iff.mp (Fact.out : p.Prime).ne_one)).mp hpow_dvd
  have he_le_a : e ≤ a := he_le_k.trans hk_le_a
  have hdiff_dvd := prime_dvd_card_sub_card_fixedPoints_of_pgroup_action (X := X) hA
  have hcard_eq : Nat.card X = Nat.card F * p ^ e := by
    calc
      Nat.card X = F.index * Nat.card F := F.index_mul_card.symm
      _ = p ^ e * Nat.card F := by rw [he_index]
      _ = Nat.card F * p ^ e := by rw [mul_comm]
  have hdiff_eq : Nat.card X - Nat.card (MulAction.fixedPoints A X) =
      Nat.card F * (p ^ e - 1) := by
    change Nat.card X - Nat.card F = Nat.card F * (p ^ e - 1)
    rw [hcard_eq]
    simpa [mul_one] using (Nat.mul_sub_left_distrib (Nat.card F) (p ^ e) 1).symm
  have hq_dvd_mul : q ∣ Nat.card F * (p ^ e - 1) := by
    rwa [← hdiff_eq]
  obtain ⟨r, hF_card_pow⟩ := IsPGroup.iff_card.mp (hX.to_subgroup F)
  have hq_coprime_cardF : q.Coprime (Nat.card F) := by
    rw [hF_card_pow]
    exact
      ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr hpq).pow_right r
  have hq_dvd : q ∣ p ^ e - 1 := hq_coprime_cardF.dvd_of_dvd_mul_left hq_dvd_mul
  exact ⟨e, he_pos, he_le_a, hq_dvd⟩

/-- **Isaacs Cor 5.29**: If `|G| = p^a m`, `p ∤ m`, and no prime divisor `q`
of `m` divides any `p^e - 1` with `1 ≤ e ≤ a`, then `G` has a normal
p-complement.

**Proof** (Isaacs p.179): use Frobenius' p-local criterion. If a q-subgroup `Q`
normalizing a p-subgroup `X` acts nontrivially, then the fixed-point subgroup
`C_X(Q)` is proper in `X`; orbit counting gives `q ∣ |X| - |C_X(Q)|`, hence
`q ∣ p^e - 1` for `|X:C_X(Q)| = p^e`, contradiction. -/
theorem hasNormalPComplement_of_no_prime_dvd_pow_sub_one
    [Finite G] {p a m : ℕ} [Fact p.Prime]
    (hcard : Nat.card G = p ^ a * m) (hpm : ¬ p ∣ m)
    (hNo : ∀ {q e : ℕ}, q.Prime → q ∣ m → 1 ≤ e → e ≤ a →
      ¬ q ∣ p ^ e - 1) :
    HasNormalPComplement p G := by
  classical
  refine hasNormalPComplement_of_prime_subgroups_centralize
    (fun {q} _ hq_ne_p {X Q} hXp hQq hQ_le_N => ?_)
  by_contra hQ_not_le_C
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN_def
  let QN : Subgroup N := Q.subgroupOf N
  have hQN_q : IsPGroup q QN := by
    have h_iso : QN ≃* Q := Subgroup.subgroupOfEquivOfLe hQ_le_N
    exact hQq.of_equiv h_iso.symm
  have hfix_ne : MulAction.fixedPoints QN X ≠ Set.univ := by
    intro hfix_univ
    apply hQ_not_le_C
    intro y hyQ
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    let yN : N := ⟨y, by simpa [hN_def] using hQ_le_N hyQ⟩
    let yQN : QN := ⟨yN, by rw [Subgroup.mem_subgroupOf]; exact hyQ⟩
    let xX : X := ⟨x, hxX⟩
    have hfixed : yQN • xX = xX := by
      have hx_fixed : xX ∈ MulAction.fixedPoints QN X := by
        rw [hfix_univ]
        exact Set.mem_univ xX
      exact hx_fixed yQN
    have hconj : y * x * y⁻¹ = x := by
      exact congrArg Subtype.val hfixed
    calc x * y = (y * x * y⁻¹) * y := by rw [hconj]
      _ = y * x := by group
  have hQ_ne_bot : Q ≠ ⊥ := by
    intro hQ_bot
    apply hQ_not_le_C
    intro y hyQ
    rw [Subgroup.mem_centralizer_iff]
    intro x _hxX
    have hy_one : y = 1 := by
      rw [hQ_bot, Subgroup.mem_bot] at hyQ
      exact hyQ
    rw [hy_one, one_mul, mul_one]
  have hQ_card_ne_one : Nat.card Q ≠ 1 := by
    intro hcardQ
    exact hQ_ne_bot (Subgroup.card_eq_one.mp hcardQ)
  have hQ_card_gt_one : 1 < Nat.card Q := by
    have hpos : 0 < Nat.card Q := Nat.card_pos
    omega
  haveI : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp hQ_card_gt_one
  obtain ⟨n, hn_pos, hQ_card_eq⟩ := hQq.nontrivial_iff_card.mp inferInstance
  have hq_dvd_Q : q ∣ Nat.card Q := by
    rw [hQ_card_eq]
    exact dvd_pow_self q (ne_of_gt hn_pos)
  have hq_dvd_G : q ∣ Nat.card G := by
    have hQ_dvd_top : Nat.card Q ∣ Nat.card (⊤ : Subgroup G) :=
      Subgroup.card_dvd_of_le (show Q ≤ (⊤ : Subgroup G) from le_top)
    exact hq_dvd_Q.trans (by simpa using hQ_dvd_top)
  have hq_dvd_m : q ∣ m := by
    have hq_dvd_mul : q ∣ p ^ a * m := by
      rwa [← hcard]
    rcases (Fact.out : q.Prime).dvd_mul.mp hq_dvd_mul with hq_dvd_pa | hq_dvd_m
    · have hcop_q_pa : q.Coprime (p ^ a) :=
        ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr
          hq_ne_p).pow_right a
      exact False.elim (((Fact.out : q.Prime).coprime_iff_not_dvd.mp hcop_q_pa) hq_dvd_pa)
    · exact hq_dvd_m
  have hX_bound : ∃ k, k ≤ a ∧ Nat.card X = p ^ k := by
    obtain ⟨k, hkX⟩ := IsPGroup.iff_card.mp hXp
    refine ⟨k, ?_, hkX⟩
    have hX_card_dvd_G : Nat.card X ∣ Nat.card G := by
      have hX_dvd_top : Nat.card X ∣ Nat.card (⊤ : Subgroup G) :=
        Subgroup.card_dvd_of_le (show X ≤ (⊤ : Subgroup G) from le_top)
      simpa using hX_dvd_top
    have hpk_dvd_pa_m : p ^ k ∣ p ^ a * m := by
      rw [← hcard, ← hkX]
      exact hX_card_dvd_G
    have hcop_pk_m : (p ^ k).Coprime m :=
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpm).pow_left k
    have hpk_dvd_pa : p ^ k ∣ p ^ a :=
      hcop_pk_m.dvd_of_dvd_mul_left (by rwa [mul_comm] at hpk_dvd_pa_m)
    exact (pow_dvd_pow_iff (Fact.out : p.Prime).ne_zero
      (mt Nat.isUnit_iff.mp (Fact.out : p.Prime).ne_one)).mp hpk_dvd_pa
  obtain ⟨e, he_pos, he_le_a, hq_dvd_pe⟩ :=
    exists_prime_dvd_pow_sub_one_of_nontrivial_pgroup_action
      (A := QN) (X := X) hXp hQN_q hq_ne_p hX_bound hfix_ne
  exact (hNo (q := q) (e := e) (Fact.out : q.Prime) hq_dvd_m he_pos he_le_a
    hq_dvd_pe).elim

/-- **Isaacs Cor 5.30** (p odd 中心化): ⭐ **FT 経路で奇数位数仮定との親和性**.
`p` odd, 全 order-`p` 元が `Z(G)` 中心 ⇒ `G` は normal p-complement を持つ.

**証明** (Isaacs p.180): Thm 5.26 で any p-subgroup X に対し N_G(X)/C_G(X) が p-group
を示せばよい. `Q := N_G(X)/C_G(X)` 内の p'-部分 A を取り A が trivial に作用することを
**Ch.4 Thm 4.36** (p>2 + p-群 G + p'-A が order-p 元固定 ⇒ A trivial) で示す. 仮定より
order-p 元は中心で A 不変, 中心で固定 ⇒ Thm 4.36 適用条件成立.

**実装状態**: Ch.4 §4D Thm 4.36 を q-subgroup action に適用して完成. -/
theorem normal_p_complement_of_order_p_central_odd
    [Finite G] {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hCent : ∀ g : G, orderOf g = p → g ∈ Subgroup.center G) :
    HasNormalPComplement p G := by
  classical
  refine hasNormalPComplement_of_prime_subgroups_centralize
    (fun {q} _ hq_ne_p {X Q} hXp hQq hQ_le_N => ?_)
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN_def
  let QN : Subgroup N := Q.subgroupOf N
  have hQN_q : IsPGroup q QN := by
    have h_iso : QN ≃* Q := Subgroup.subgroupOfEquivOfLe hQ_le_N
    exact hQq.of_equiv h_iso.symm
  let φ : QN →* MulAut X := MulDistribMulAction.toMulAut QN X
  have hQN_p' : ¬ p ∣ Nat.card QN := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQN_q
    rw [hn]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp
      (((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr
        hq_ne_p.symm).pow_right n)
  have hfix : ∀ x : X, x ^ p = 1 → ∀ a : QN, (φ a) x = x := by
    intro x hxpow a
    apply Subtype.ext
    have hxpowG : (x : G) ^ p = 1 := by
      exact congrArg Subtype.val hxpow
    have hxord_dvd : orderOf (x : G) ∣ p := orderOf_dvd_of_pow_eq_one hxpowG
    change ((a : QN) • x : X).val = x.val
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hxord_dvd with hxord1 | hxordp
    · have hx_one : (x : G) = 1 := orderOf_eq_one_iff.mp hxord1
      have hx_one_X : x = 1 := Subtype.ext hx_one
      simp [hx_one_X]
    · have hx_cent : (x : G) ∈ Subgroup.center G := hCent x hxordp
      have hcomm : (a : N).val * (x : G) = (x : G) * (a : N).val :=
        Subgroup.mem_center_iff.mp hx_cent (a : N).val
      change (a : N).val * (x : G) * (a : N).val⁻¹ = (x : G)
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hbot : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
    OddOrder.Isaacs.Ch04.isaacs_thm_4_36 hp_odd φ hXp hQN_p' hfix
  have htriv : ∀ a : QN, ∀ x : X, (φ a) x = x :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially φ).mp hbot
  intro y hyQ
  rw [Subgroup.mem_centralizer_iff]
  intro x hxX
  let yN : N := ⟨y, by simpa [hN_def] using hQ_le_N hyQ⟩
  let yQN : QN := ⟨yN, by rw [Subgroup.mem_subgroupOf]; exact hyQ⟩
  let xX : X := ⟨x, hxX⟩
  have hfixed : (φ yQN) xX = xX := htriv yQN xX
  have hconj : y * x * y⁻¹ = x := by
    exact congrArg Subtype.val hfixed
  calc x * y = (y * x * y⁻¹) * y := by rw [hconj]
    _ = y * x := by group

end -- 5E

end OddOrder.Isaacs.Ch05

