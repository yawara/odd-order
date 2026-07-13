/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7B1_NormalJ

/-!
# Isaacs FGT Ch.7 (Thompson subgroup) — S7B part 2 + S7C: normal-J close + Thm 7.1 proof + Thm 7.7 (pp. 209-219)
-/

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### Step 4-5-8 closing axioms (mmd L3870-3896)

The Goldschmidt-style closing argument combines:

* **Step 4** (mmd L3870): `G = LA` and `P = UA` (using induction hypothesis on
  the proper subgroup `H = LA` to reach a contradiction unless `H = G`).
* **Step 5** (mmd L3874): `|Ā| = p`, using Lemma 6.20 (cyclic faithful coprime
  action) applied to `Ā ↷ L̅` (faithful by Step 1(c), coprime by p / p').  The
  Step 6.20 hypothesis "trivial on every proper invariant subgroup" comes from
  Step 3 applied to `MA` for any `Ā`-invariant `M̅ < L̅`.
* **Step 8** (mmd L3893-3896): combines |V : V∩A| ≤ p (Step 7, landed) with
  `P̄ = Ā` (from Step 4) and `Ā` abelian centralizing `V∩A` to derive
  `|V : C_V(P̄)| ≤ p`, then applies Thm 7.5 (`sylow_normal_of_elementary_normal_P_theorem`)
  to get `P̄ ⊴ Ḡ`, then pulls back to `P ⊴ G` and `A ⊆ P ⊆ U`, contradicting
  `A ⊄ U`.

We split the remaining work into three focused axioms (each tracking a single
textbook step), so future sessions can discharge them independently:

* `step4_5_LA_eq_top_and_Abar_card_eq_p`: Steps 4 + 5 combined (they share the
  same induction-hypothesis usage via Step 3).  Produces `P = UA ∧ Nat.card Ā = p`.
* `step8_normal_via_thm75`: Step 8's Thm 7.5 application (Ḡ ↷ V faithful with
  the |V : C_V(P̄)| ≤ p bound to `P̄ ⊴ Ḡ`).
* `step8_pullback`: pulling back `P̄ ⊴ Ḡ` to `P ⊴ G` and concluding `A ⊆ U`.

The glue between them is proved as actual theorem code.

Tracking issue: [`issues/0036-stuck-7-6-step-7.md`](../../../issues/0036-stuck-7-6-step-7.md). -/

/-- **Isaacs Thm 7.6 Step 1(b)** (mmd L3843): if `U = O_p(G) ≤ H ≤ G` then
`O_{p'}(H) = 1`.

Book argument: write `M = O_{p'}(H)`.  Both `M` and `U` (as `U.subgroupOf H`)
are normal `H`-subgroups with coprime orders (`M` a `p'`-group, `U` a `p`-group),
so they commute; hence `M` (mapped into `G`) lies in `C_G(U) ≤ U` (Hall-Higman
3.21, hypothesis (iv)).  But `M` is a `p'`-group inside the `p`-group `U`, so
`M = 1`. -/
theorem oPiCorePrime_subgroup_eq_bot_of_opCore_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    {H : Subgroup G} (hUH : OddOrder.Isaacs.Ch01.opCore p G ≤ H) :
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) = ⊥ := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set M : Subgroup (↥H) := OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) with hM_def
  -- `M` is a `{q ≠ p}`-group.
  have hM_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} M :=
    OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := ↥H) {q | q ≠ p}
  -- `U` lives inside `H` as `U.subgroupOf H = U.comap H.subtype`, normal in `↥H`.
  have hU_le_H : U ≤ H := hUH
  set Usub : Subgroup (↥H) := U.subgroupOf H with hUsub_def
  haveI hUsub_normal : Usub.Normal :=
    (OddOrder.Isaacs.Ch01.opCore.normal p G).subgroupOf H
  -- `Usub` is a `p`-group (`comap` of the `p`-group `U` along an injective hom).
  have hU_pg : IsPGroup p ↥U := OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hUsub_pg : IsPGroup p ↥Usub := hU_pg.comap_subtype
  obtain ⟨k, hUsub_card⟩ : ∃ k, Nat.card ↥Usub = p ^ k := IsPGroup.iff_card.mp hUsub_pg
  -- `M ⊓ Usub = ⊥`: coprime cards (`p ∤ |M|` since `M` is `{q≠p}`).
  have hp_not_dvd_M : ¬ p ∣ Nat.card M := by
    intro hdvd
    have hp_pf : p ∈ (Nat.card M).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
    exact (hM_pi p hp_pf) rfl
  have hcoprime : Nat.Coprime (Nat.card M) (Nat.card ↥Usub) := by
    rw [hUsub_card]
    have hp_cop : Nat.Coprime p (Nat.card M) :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_M
    exact (hp_cop.symm).pow_right k
  have h_disj : Disjoint M Usub := disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime hcoprime)
  -- `M` commutes with `Usub` (both normal, disjoint).
  have h_comm : ∀ m ∈ M, ∀ u ∈ Usub, (m : ↥H) * u = u * m := fun m hm u hu =>
    Subgroup.commute_of_normal_of_disjoint M Usub
      (OddOrder.Isaacs.Ch03.oPiCore.normal {q | q ≠ p} (↥H)) hUsub_normal h_disj
      m u hm hu
  -- Map `M` into `G`.
  set M' : Subgroup G := M.map H.subtype with hM'_def
  -- `M' ≤ C_G(U)`.
  have hM'_le_centralizer : M' ≤ Subgroup.centralizer (U : Set G) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu_H : u ∈ H := hU_le_H hu
    have hu_Usub : (⟨u, hu_H⟩ : ↥H) ∈ Usub := by
      rw [hUsub_def, Subgroup.mem_subgroupOf]; exact hu
    have hval := congrArg (Subtype.val : ↥H → G) (h_comm m hm ⟨u, hu_H⟩ hu_Usub)
    simpa using hval.symm
  -- `C_G(U) ≤ U` (Hall-Higman) ⇒ `M' ≤ U`.
  have hM'_le_U : M' ≤ U := hM'_le_centralizer.trans
    (centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot h_oPiPrime_trivial)
  -- `M'` is a `p`-group (inside `U`) and `Nat.card M' = Nat.card M` (injective map);
  -- but `p ∤ Nat.card M`, so `Nat.card M' = 1`, hence `M' = ⊥`, hence `M = ⊥`.
  have hM'_card : Nat.card ↥M' = Nat.card M := by
    rw [hM'_def]
    exact Nat.card_congr (Subgroup.equivMapOfInjective M H.subtype Subtype.coe_injective).symm.toEquiv
  have hM'_pg : IsPGroup p ↥M' :=
    hU_pg.of_injective (Subgroup.inclusion hM'_le_U) (Subgroup.inclusion_injective hM'_le_U)
  obtain ⟨j, hj⟩ : ∃ j, Nat.card ↥M' = p ^ j := IsPGroup.iff_card.mp hM'_pg
  have hj_zero : j = 0 := by
    by_contra hj_ne
    apply hp_not_dvd_M
    rw [← hM'_card, hj]
    exact dvd_pow_self p hj_ne
  have hM'_card_one : Nat.card ↥M' = 1 := by rw [hj, hj_zero, pow_zero]
  have hM'_bot : M' = ⊥ := Subgroup.card_eq_one.mp hM'_card_one
  -- `M.map H.subtype = ⊥` with injective `H.subtype` ⇒ `M = ⊥`.
  have hM_le_ker : M ≤ (H.subtype).ker := by
    rw [← Subgroup.map_eq_bot_iff]; exact hM'_bot
  rw [Subgroup.ker_subtype] at hM_le_ker
  exact le_bot_iff.mp hM_le_ker

/-- **Isaacs Thm 7.6 Step 3 hypothesis (v)** (mmd L3852): for an intermediate
subgroup `U ≤ H ≤ G`, the Sylow `S = H ∩ P` of `↥H` satisfies `C_H(Z(S)) = S`.

Book proof: `Z(P) ⊆ U ⊆ S ⊆ P` gives `Z(P) ⊆ Z(S)`, so
`C_H(Z(S)) ⊆ C_G(Z(P)) = P` (hypothesis (v) on `G`), a `p`-subgroup of `H`
containing the Sylow `S`; maximality forces equality. -/
private theorem centralizer_center_sylow_subgroup_eq_self_of_intermediate
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {H : Subgroup G}
    (hU_le_H : OddOrder.Isaacs.Ch01.opCore p G ≤ H)
    (S : Sylow p ↥H)
    (hS_eq : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H) :
    Subgroup.centralizer
        (((Subgroup.center (S : Subgroup ↥H)).map (S : Subgroup ↥H).subtype) : Set ↥H)
      = (S : Subgroup ↥H) := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  -- `S` mapped to `G` is `H ⊓ P`.
  have hS_map : (S : Subgroup ↥H).map H.subtype = H ⊓ (P : Subgroup G) := by
    rw [hS_eq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  have hS_le_P : (S : Subgroup ↥H).map H.subtype ≤ (P : Subgroup G) := by
    rw [hS_map]; exact inf_le_right
  -- `U ≤ S` (as `U.subgroupOf H ≤ S`), so `Z(P)` image ⊆ image of S.
  have hU_le_HP : U ≤ H ⊓ (P : Subgroup G) := le_inf hU_le_H (OddOrder.Isaacs.Ch01.opCore_le P)
  -- `Z(P).map P.subtype ≤ U` (Step 1a).
  have hZP_le_U : (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤ U :=
    center_sylow_le_opCore_of_oPiCorePrime_eq_bot h_oPiPrime_trivial P
  -- Abbreviation: `ZS := Z(S).map S.subtype` (subgroup of `↥H`), `ZSG := ZS.map H.subtype`.
  set ZS : Subgroup ↥H := (Subgroup.center (S : Subgroup ↥H)).map (S : Subgroup ↥H).subtype
    with hZS_def
  refine le_antisymm ?_ ?_
  · -- `C_H(ZS) ≤ S`.  Map to `G`: contained in `C_G(Z(P)-image) = P`, p-subgroup ⊇ S.
    -- Step (a): `Z(P).map P.subtype ≤ ZS.map H.subtype` (central elts of P, lying in S,
    -- are central in S).
    have hZPG_le_ZSG :
        (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
          ZS.map H.subtype := by
      rintro _ ⟨z, hz_center, rfl⟩
      -- `(z : G) ∈ U ≤ H ⊓ P`, so `z` corresponds to an element of `S`.
      have hzG_U : ((z : (P : Subgroup G)) : G) ∈ U :=
        hZP_le_U ⟨z, hz_center, rfl⟩
      have hzG_H : ((z : (P : Subgroup G)) : G) ∈ H := hU_le_H hzG_U
      have hzG_P : ((z : (P : Subgroup G)) : G) ∈ (P : Subgroup G) := z.property
      -- `z` as element of `↥H`.
      set zH : ↥H := ⟨((z : (P : Subgroup G)) : G), hzG_H⟩ with hzH_def
      have hzH_S : zH ∈ (S : Subgroup ↥H) := by
        rw [hS_eq, Subgroup.mem_subgroupOf]
        exact ⟨hzG_H, hzG_P⟩
      -- `zH` is central in `S`: it commutes with every element of `S` (via `z ∈ Z(P)`, `S ≤ P`).
      have hzH_center : (⟨zH, hzH_S⟩ : (S : Subgroup ↥H)) ∈
          Subgroup.center (S : Subgroup ↥H) := by
        rw [Subgroup.mem_center_iff]
        intro s
        -- `s : ↥(S:Subgroup ↥H)`, its image in `G` lies in `P`.
        have hsG_P : (((s : (S : Subgroup ↥H)) : ↥H) : G) ∈ (P : Subgroup G) := by
          have hmem : (((s : (S : Subgroup ↥H)) : ↥H) : G) ∈
              (S : Subgroup ↥H).map H.subtype :=
            Subgroup.mem_map_of_mem H.subtype s.property
          exact hS_le_P hmem
        apply Subtype.ext; apply Subtype.ext
        -- `z` central in `P` commutes with `s`-image: `s_G * z_G = z_G * s_G`.
        have hcomm := Subgroup.mem_center_iff.mp hz_center
          (⟨(((s : (S : Subgroup ↥H)) : ↥H) : G), hsG_P⟩ : (P : Subgroup G))
        have hval := congrArg (fun x : (P : Subgroup G) => (x : G)) hcomm
        -- Goal (after two `Subtype.ext`): `s_G * z_G = z_G * s_G`.
        simpa [hzH_def] using hval
      -- So `zH.val (in G) ∈ ZS.map H.subtype`.
      exact ⟨zH, ⟨⟨zH, hzH_S⟩, hzH_center, rfl⟩, rfl⟩
    -- Step (b): `(C_H(ZS)).map H.subtype ≤ C_G(ZS.map H.subtype)`.
    have hcent_map :
        (Subgroup.centralizer (ZS : Set ↥H)).map H.subtype ≤
          Subgroup.centralizer ((ZS.map H.subtype) : Set G) := by
      rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have hcomm : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hc w hw).symm
      exact congrArg (fun x : ↥H => (x : G)) hcomm.symm
    -- Combine: `(C_H(ZS)).map H.subtype ≤ C_G(Z(P)-image) = P`.
    have hcent_le_P : (Subgroup.centralizer (ZS : Set ↥H)).map H.subtype ≤ (P : Subgroup G) := by
      refine hcent_map.trans ?_
      have hmono : Subgroup.centralizer ((ZS.map H.subtype) : Set G) ≤
          Subgroup.centralizer
            (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G) :=
        Subgroup.centralizer_le hZPG_le_ZSG
      rw [h_centralizer_center] at hmono
      exact hmono
    -- `C_H(ZS) ≤ P.subgroupOf H` (a `p`-group), containing the Sylow `S` ⇒ equal.
    have hcent_le_Psub :
        Subgroup.centralizer (ZS : Set ↥H) ≤ (P : Subgroup G).subgroupOf H := by
      intro c hc
      rw [Subgroup.mem_subgroupOf]
      have : (c : G) ∈ (P : Subgroup G) := hcent_le_P ⟨c, hc, rfl⟩
      exact this
    have hPsub_pg : IsPGroup p ↥((P : Subgroup G).subgroupOf H) :=
      P.isPGroup'.comap_subtype
    have hcent_pg : IsPGroup p ↥(Subgroup.centralizer (ZS : Set ↥H)) :=
      hPsub_pg.of_injective (Subgroup.inclusion hcent_le_Psub)
        (Subgroup.inclusion_injective hcent_le_Psub)
    -- `S ≤ C_H(ZS)` (next bullet), so the Sylow `S` is inside the `p`-subgroup `C_H(ZS)`.
    have hS_le_cent : (S : Subgroup ↥H) ≤ Subgroup.centralizer (ZS : Set ↥H) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have hcomm : (⟨s, hs⟩ : (S : Subgroup ↥H)) * w = w * ⟨s, hs⟩ :=
        Subgroup.mem_center_iff.mp hw ⟨s, hs⟩
      exact congrArg (fun x : (S : Subgroup ↥H) => (x : ↥H)) hcomm.symm
    exact (S.is_maximal' hcent_pg hS_le_cent).le
  · -- `S ≤ C_H(ZS)`: every `s ∈ S` centralizes `Z(S) ⊆ S`.
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have hcomm : (⟨s, hs⟩ : (S : Subgroup ↥H)) * w = w * ⟨s, hs⟩ :=
      Subgroup.mem_center_iff.mp hw ⟨s, hs⟩
    exact congrArg (fun x : (S : Subgroup ↥H) => (x : ↥H)) hcomm.symm

/-- **Isaacs Thm 7.6 Step 3** (mmd L3850-3856): the IH-consuming core of the
Goldschmidt argument.

Given `U·A ≤ H` with `H` a **proper** subgroup of `G` and `H ∩ P ∈ Syl_p(H)`,
the conclusion is `⁅L ⊓ H, A⁆ ≤ U`, i.e. `Ā` centralizes `(L ∩ H)bar` in
`Ḡ = G/U`.  Here `L = O_{p',p}(G)` (`opPpPrimeCore`), `U = O_p(G)`.

Book proof (mmd L3850-3856):
* `H` satisfies the five Thm 7.6 hypotheses: (i) `p`-separable (subgroup),
  (ii) `p ≠ 2`, (iii) Sylow-2 abelian (descent), (iv) `O_{p'}(H) = 1`
  (`oPiCorePrime_subgroup_eq_bot_of_opCore_le`, landed), and (v)
  `C_H(Z(S)) = S` for `S = H ∩ P`
  (`centralizer_center_sylow_subgroup_eq_self_of_intermediate`, landed).
* By the IH (`H < G`), `J(S) ⊴ H`.  Since `A ∈ E(P)` and `A ⊆ S ⊆ P`,
  `A ∈ E(S)`, so `A ⊆ J(S)`.
* `⁅L ⊓ H, A⁆ ⊆ ⁅L ⊓ H, J(S)⁆ ⊆ (L ⊓ H) ⊓ J(S)` (both normal in `H`)
  `⊆ L ⊓ J(S) ⊆ U` (`U` is the unique Sylow-`p` of `L`).

Hypothesis (v) is the landed
`centralizer_center_sylow_subgroup_eq_self_of_intermediate`. -/
private theorem step3_Abar_centralizes_inter_LBar.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (ih : ∀ (H : Type u) [Group H] [Finite H]
      [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H],
      Nat.card H < Nat.card G →
      (∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ →
      ∀ (Q : Sylow p H),
        Subgroup.centralizer
            (((Subgroup.center (Q : Subgroup H)).map
              (Q : Subgroup H).subtype) : Set H)
          = (Q : Subgroup H) →
        (Subgroup.thompsonJ (Q : Subgroup H) p).Normal)
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    {H : Subgroup G}
    (hH_ne_top : H ≠ ⊤)
    (hUA_le_H : OddOrder.Isaacs.Ch01.opCore p G ⊔ A ≤ H)
    (S : Sylow p ↥H)
    (hS_eq : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H) :
    (⁅opPpPrimeCore G p ⊓ H, A⁆ : Subgroup G) ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set L : Subgroup G := opPpPrimeCore G p with hL_def
  have hU_le_H : U ≤ H := le_sup_left.trans hUA_le_H
  have hA_le_H : A ≤ H := le_sup_right.trans hUA_le_H
  have hA_le_P : A ≤ (P : Subgroup G) := hA_mem.1
  -- `S` mapped to `G` is `H ⊓ P`.
  have hS_map : (S : Subgroup ↥H).map H.subtype = H ⊓ (P : Subgroup G) := by
    rw [hS_eq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  -- (a) `Nat.card ↥H < Nat.card G` (since `H ≠ ⊤`).
  have hcard_lt : Nat.card ↥H < Nat.card G := by
    have hidx : 1 < H.index := Subgroup.one_lt_index_of_ne_top hH_ne_top
    have hmul : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
    calc Nat.card ↥H = Nat.card ↥H * 1 := (mul_one _).symm
      _ < Nat.card ↥H * H.index := (Nat.mul_lt_mul_left Nat.card_pos).mpr hidx
      _ = Nat.card G := hmul
  -- (b) Descend hypotheses to `↥H`.
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) (↥H) :=
    OddOrder.Isaacs.Ch03.Subgroup.isPiSeparable_of_isPiSeparable ({p} : Set ℕ) H
  have h2abelian' : ∀ T : Subgroup ↥H, IsPGroup 2 T → ∀ x y : ↥T, x * y = y * x := by
    intro T hT2
    have hTG2 : IsPGroup 2 (T.map H.subtype) := hT2.map H.subtype
    have hTGcomm := h2abelian (T.map H.subtype) hTG2
    intro a b
    apply Subtype.ext; apply Subtype.ext
    have h := hTGcomm ⟨((a : ↥H) : G), ⟨(a : ↥H), a.property, rfl⟩⟩
      ⟨((b : ↥H) : G), ⟨(b : ↥H), b.property, rfl⟩⟩
    exact congrArg (fun z : ↥(T.map H.subtype) => (z : G)) h
  have h_oPi' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) = ⊥ :=
    oPiCorePrime_subgroup_eq_bot_of_opCore_le h_oPiPrime_trivial hU_le_H
  -- Hypothesis (v) for `S`.
  have hv : Subgroup.centralizer
        (((Subgroup.center (S : Subgroup ↥H)).map (S : Subgroup ↥H).subtype) : Set ↥H)
      = (S : Subgroup ↥H) :=
    centralizer_center_sylow_subgroup_eq_self_of_intermediate h_oPiPrime_trivial P
      h_centralizer_center hU_le_H S hS_eq
  -- (c) IH: `J(S) ⊴ ↥H`.
  have hJS_normal : (Subgroup.thompsonJ (S : Subgroup ↥H) p).Normal :=
    ih (↥H) hcard_lt h2abelian' h_oPi' S hv
  -- (d) `A.subgroupOf H ∈ maxElemAbelianIn S p`, hence `A.subgroupOf H ≤ J(S)`.
  have hAsub_le_S : A.subgroupOf H ≤ (S : Subgroup ↥H) := by
    rw [hS_eq]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨x.property, hA_le_P hx⟩
  -- `A.subgroupOf H ≃* A` (since `A ≤ H`), preserving cardinality and elem-ab.
  have hAsub_equiv := Subgroup.subgroupOfEquivOfLe hA_le_H
  have hAsub_card : Nat.card ↥(A.subgroupOf H) = Nat.card ↥A :=
    Nat.card_congr hAsub_equiv.toEquiv
  have hAsub_el : (A.subgroupOf H).IsElementaryAbelian p := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · exact hAsub_equiv.injective (by
        rw [map_mul, map_mul]; exact (hA_mem.2.1).comm (hAsub_equiv x) (hAsub_equiv y))
    · exact hAsub_equiv.injective (by
        rw [map_pow, map_one]; exact (hA_mem.2.1).pow_eq_one (hAsub_equiv x))
  have hAsub_mem : A.subgroupOf H ∈ Subgroup.maxElemAbelianIn (S : Subgroup ↥H) p := by
    refine ⟨hAsub_le_S, hAsub_el, ?_⟩
    intro F hF_S hF_el
    -- `F.map H.subtype ≤ H ⊓ P ≤ P` is elem-ab; `A ∈ E(P)` ⇒ `|F| ≤ |A|`.
    have hFmap_le_P : F.map H.subtype ≤ (P : Subgroup G) := by
      have : F.map H.subtype ≤ (S : Subgroup ↥H).map H.subtype := Subgroup.map_mono hF_S
      rw [hS_map] at this
      exact this.trans inf_le_right
    have hFmap_el : (F.map H.subtype).IsElementaryAbelian p :=
      isElementaryAbelian_map_of_isElementaryAbelian H.subtype hF_el
    have hFmap_card : Nat.card ↥(F.map H.subtype) = Nat.card ↥F :=
      Nat.card_congr (Subgroup.equivMapOfInjective F H.subtype Subtype.coe_injective).symm.toEquiv
    have hle := hA_mem.2.2 (F.map H.subtype) hFmap_le_P hFmap_el
    rw [hFmap_card] at hle
    rw [← hAsub_card] at hle
    exact hle
  have hAsub_le_JS : A.subgroupOf H ≤ Subgroup.thompsonJ (S : Subgroup ↥H) p :=
    Subgroup.le_thompsonJ_of_mem_maxElemAbelianIn hAsub_mem
  -- (e) Commutator chain in `↥H`: `⁅L.subgroupOf H, A.subgroupOf H⁆ ≤ U.subgroupOf H`.
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  -- `L.subgroupOf H` is normal in `↥H` (L ⊴ G).
  haveI hLsub_normal : (L.subgroupOf H).Normal := by
    rw [hL_def]; exact (opPpPrimeCore_normal (G := G) (p := p)).subgroupOf H
  -- `J(S) ≤ S ≤ P`, so `J(S).map H.subtype` is a `p`-subgroup of `G` inside `P`.
  have hJS_le_S : Subgroup.thompsonJ (S : Subgroup ↥H) p ≤ (S : Subgroup ↥H) :=
    Subgroup.thompsonJ_le _ _
  have hJSmap_le_P : (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤ (P : Subgroup G) := by
    have : (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤
        (S : Subgroup ↥H).map H.subtype := Subgroup.map_mono hJS_le_S
    rw [hS_map] at this
    exact this.trans inf_le_right
  -- `⁅L.subgroupOf H, A.subgroupOf H⁆ ≤ ⁅L.subgroupOf H, J(S)⁆ ≤ (L.subgroupOf H) ⊓ J(S)`.
  haveI := hJS_normal
  have hchain : (⁅L.subgroupOf H, A.subgroupOf H⁆ : Subgroup ↥H) ≤
      (L.subgroupOf H) ⊓ Subgroup.thompsonJ (S : Subgroup ↥H) p := by
    refine le_trans (Subgroup.commutator_mono le_rfl hAsub_le_JS) ?_
    exact Subgroup.commutator_le_inf (L.subgroupOf H) (Subgroup.thompsonJ (S : Subgroup ↥H) p)
  -- Map the chain back to `G`: `⁅L ⊓ H, A⁆ ≤ ((L.subgroupOf H) ⊓ J(S)).map H.subtype`.
  have hcomm_map_eq : (⁅L.subgroupOf H, A.subgroupOf H⁆ : Subgroup ↥H).map H.subtype =
      ⁅(L ⊓ H), A⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA_le_H, inf_comm L H]
  -- The target `⁅L ⊓ H, A⁆ ≤ U`.
  have hgoal_map : ⁅(L ⊓ H), A⁆ ≤ ((L.subgroupOf H) ⊓
      Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype := by
    rw [← hcomm_map_eq]; exact Subgroup.map_mono hchain
  -- `((L.subgroupOf H) ⊓ J(S)).map H.subtype ≤ L ⊓ (J(S).map H.subtype)`.
  have hinf_map_le : ((L.subgroupOf H) ⊓ Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤
      L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype := by
    rintro _ ⟨x, ⟨hxL, hxJ⟩, rfl⟩
    refine ⟨?_, Subgroup.mem_map_of_mem _ hxJ⟩
    have : (x : G) ∈ L := hxL
    exact this
  -- `L ⊓ (p-subgroup) ≤ U`: any `p`-subgroup of `L` lies in `U` (since `L/U` is `p'`).
  have hLinf_le_U : L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤ U := by
    -- `K := L ⊓ J(S).map` is a `p`-group (≤ J(S).map ≤ P).
    have hK_le_P : L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤
        (P : Subgroup G) := inf_le_right.trans hJSmap_le_P
    have hK_pg : IsPGroup p ↥(L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype) :=
      P.isPGroup'.of_injective (Subgroup.inclusion hK_le_P) (Subgroup.inclusion_injective hK_le_P)
    -- `K ≤ L`, and `K.map mk` is a `p`-group inside `L̄ = O_{p'}(Ḡ)`, hence trivial ⇒ `K ≤ U`.
    intro x hx
    have hxL : x ∈ L := hx.1
    -- `mk x ∈ L̄` and `mk x` lies in the `p`-group image, but `L̄` is `p'`, so `mk x = 1`.
    have hKmap_pg : IsPGroup p ((L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype).map mk) :=
      hK_pg.map mk
    have hxbar_mem : mk x ∈ (L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype).map mk :=
      Subgroup.mem_map_of_mem mk hx
    have hxbar_Lbar : mk x ∈ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
      have hLmap : L.map mk = OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
        rw [hL_def, hmk_def]; exact opPpPrimeCore_map_eq_LBar
      rw [← hLmap]; exact Subgroup.mem_map_of_mem mk hxL
    -- `mk x` has order a power of `p` (in the image) and divides `|L̄|` (a `p'`-number) ⇒ `mk x = 1`.
    have hxbar_one : mk x = 1 := by
      -- order of `mk x` divides a `p`-power (from the `p`-group `K.map mk`).
      obtain ⟨k, hk⟩ := hKmap_pg ⟨mk x, hxbar_mem⟩
      have hord_dvd_pk : orderOf (mk x) ∣ p ^ k := by
        rw [orderOf_dvd_iff_pow_eq_one]
        have hk' : (⟨mk x, hxbar_mem⟩ :
            ↥((L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype).map mk)) ^ p ^ k = 1 := hk
        have := congrArg (Subtype.val) hk'
        simpa using this
      -- order of `mk x` divides `|L̄|` (since `mk x ∈ L̄`).
      have hord_dvd_Lbar : orderOf (mk x) ∣ Nat.card (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) :=
        Subgroup.orderOf_dvd_natCard _ hxbar_Lbar
      -- `|L̄|` is a `p'`-number, so coprime to `p^k`; hence `orderOf (mk x) = 1`.
      have hp_not_dvd_Lbar : ¬ p ∣ Nat.card (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
        intro hdvd
        exact (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore
          ({p} : Set ℕ) G) {q | q ≠ p} p
          (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
      have hcop : Nat.Coprime (p ^ k) (Nat.card (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) :=
        Nat.Coprime.pow_left k ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_Lbar)
      have hord_one : orderOf (mk x) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hord_dvd_pk hord_dvd_Lbar
      exact orderOf_eq_one_iff.mp hord_one
    -- `mk x = 1 ⇒ x ∈ ker mk = U`.
    have hx_U : x ∈ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
      (QuotientGroup.eq_one_iff x).mp hxbar_one
    rwa [← hU_eq_oPi] at hx_U
  exact (hgoal_map.trans hinf_map_le).trans hLinf_le_U

/-- For `N ⊴ G` and `A` with `N ⊓ A = ⊥`, the relative index `A.relIndex (N ⊔ A)`
equals `Nat.card N`.  (Diamond isomorphism: `|NA : A| = |N : N ⊓ A| = |N|`.) -/
private theorem relIndex_sup_of_inf_eq_bot
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G} [N.Normal]
    (h_inf : N ⊓ A = ⊥) :
    A.relIndex (N ⊔ A) = Nat.card N := by
  classical
  -- `|NA| = |A| * (A.relIndex NA)` (card_mul_index inside `↥(N ⊔ A)`).
  have hA_le : A ≤ N ⊔ A := le_sup_right
  have hN_le : N ≤ N ⊔ A := le_sup_left
  have h1 : Nat.card (A.subgroupOf (N ⊔ A)) * (A.subgroupOf (N ⊔ A)).index =
      Nat.card ↥(N ⊔ A) := Subgroup.card_mul_index _
  have h1' : Nat.card A * A.relIndex (N ⊔ A) = Nat.card ↥(N ⊔ A) := by
    rw [← h1]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le).toEquiv).symm
  -- `|NA| = |N| * (N.relIndex NA)` and `N.relIndex NA = N.relIndex A = |A|`.
  have h2 : Nat.card (N.subgroupOf (N ⊔ A)) * (N.subgroupOf (N ⊔ A)).index =
      Nat.card ↥(N ⊔ A) := Subgroup.card_mul_index _
  have hNrel : (N.subgroupOf (N ⊔ A)).index = Nat.card A := by
    show N.relIndex (N ⊔ A) = Nat.card A
    rw [Subgroup.relIndex_sup_left]
    -- `N.relIndex A = |A : N ⊓ A| = |A : ⊥| = |A|`.
    show (N.subgroupOf A).index = Nat.card A
    have : N.subgroupOf A = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot]
      rw [disjoint_iff]; exact h_inf
    rw [this, Subgroup.index_bot]
  have h2' : Nat.card N * Nat.card A = Nat.card ↥(N ⊔ A) := by
    rw [← h2, hNrel]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le).toEquiv).symm
  -- Cancel `Nat.card A` from `|A| * relIndex = |N| * |A|`.
  have hA_pos : 0 < Nat.card A := Nat.card_pos
  have hfin : Nat.card A * A.relIndex (N ⊔ A) = Nat.card A * Nat.card N := by
    rw [h1', ← h2', mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hA_pos hfin

/-- **Modular law, normalizer form** (mmd L3877): if `W ≤ L`, `A ⊓ L = ⊥`, and `A`
normalizes `W`, then `(W ⊔ A) ⊓ L = W`.  Used to show `W ⊔ Ā = ⊤ ⇒ W = L̄`.

The mathlib `IsModularLattice (Subgroup ·)` instance only covers `[CommGroup]`; here
the noncommutative case is handled by hand via the product representation `W·A` of
`W ⊔ A` (valid since `A ≤ N(W)`, so `W` is normal in `W ⊔ A`). -/
private theorem inf_sup_eq_of_le_normalizer_of_inf_eq_bot
    {G : Type*} [Group G] {W A L : Subgroup G}
    (hW_le : W ≤ L) (hA_inf : A ⊓ L = ⊥) (hAnorm : A ≤ Subgroup.normalizer (W : Set G)) :
    (W ⊔ A) ⊓ L = W := by
  apply le_antisymm
  · intro x ⟨hxWA, hxL⟩
    -- `W` is normal in `A ⊔ W`, so `x = w * a` with `w ∈ W`, `a ∈ A`.
    haveI : (W.subgroupOf (A ⊔ W)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAnorm
    have hx_AW : x ∈ A ⊔ W := by rw [sup_comm]; exact hxWA
    have hmem : (⟨x, hx_AW⟩ : ↥(A ⊔ W)) ∈ (W.subgroupOf (A ⊔ W)) ⊔ (A.subgroupOf (A ⊔ W)) := by
      rw [← Subgroup.subgroupOf_sup (le_sup_right) (le_sup_left), sup_comm W A,
        Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_left] at hmem
    obtain ⟨⟨w, hw_AW⟩, hw, ⟨a, ha_AW⟩, ha, heq⟩ := hmem
    have hw_W : w ∈ W := hw
    have ha_A : a ∈ A := ha
    have hxeq : x = w * a := congrArg (Subtype.val) heq |>.symm
    -- `a = w⁻¹ * x ∈ L` (since `w ∈ W ≤ L`, `x ∈ L`), so `a ∈ A ⊓ L = ⊥`, `a = 1`.
    have ha_L : a ∈ L := by
      have : w⁻¹ * x ∈ L := L.mul_mem (L.inv_mem (hW_le hw_W)) hxL
      rwa [hxeq, ← mul_assoc, inv_mul_cancel, one_mul] at this
    have ha_one : a = 1 := by
      have : a ∈ A ⊓ L := ⟨ha_A, ha_L⟩
      rw [hA_inf, Subgroup.mem_bot] at this; exact this
    rw [hxeq, ha_one, mul_one]; exact hw_W
  · exact le_inf le_sup_left hW_le

/-- **Isaacs Thm 7.6 Step 5, "trivial on proper invariant" clause** (mmd L3876-3878).

Given the running Thm 7.6 hypotheses, the IH, the chosen `A ∈ E(P)` with `A ⊄ U`,
and Step 4's output `P = UA`, every `Ā`-invariant proper subgroup `W < L̄` of
`L̄ = O_{p'}(Ḡ)` is centralized by `Ā` (`⁅W, Ā⁆ = ⊥`).

Book proof: set `M = preimage of W in G containing U` (`= W.comap mk`), so
`U ≤ M ≤ L`.  `A ≤ N_G(M)` (since `Ā` normalizes `W` and `U = ker mk ≤ M`),
hence `H = M ⊔ A` is proper (`H = ⊤` would force `W ⊔ Ā = ⊤`, and the modular
law `(W ⊔ Ā) ⊓ L̄ = W ⊔ (Ā ⊓ L̄) = W` would give `L̄ = W`, contradicting `W < L̄`)
with `P = UA ⊆ H` Sylow (`|H : P| = |W|`, a `p'`-number, via `relIndex`).  Step 3
applied to `H` gives `⁅L ⊓ H, A⁆ ≤ U`; since `M ≤ L ⊓ H`, `⁅M, A⁆ ≤ U = ker mk`,
so `⁅W, Ā⁆ = mk⁅M, A⁆ = ⊥`. -/
private theorem step5_Abar_centralizes_invariant_proper.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (ih : ∀ (H : Type u) [Group H] [Finite H]
      [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H],
      Nat.card H < Nat.card G →
      (∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ →
      ∀ (Q : Sylow p H),
        Subgroup.centralizer
            (((Subgroup.center (Q : Subgroup H)).map
              (Q : Subgroup H).subtype) : Set H)
          = (Q : Subgroup H) →
        (Subgroup.thompsonJ (Q : Subgroup H) p).Normal)
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (h_P_eq_UA : OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G))
    {W : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)}
    (hW_le : W ≤ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))
    (hW_ne : W ≠ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))
    (hW_normalized : ∀ a : G, a ∈ A → ∀ w, w ∈ W →
      (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) a * w *
        ((QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) a)⁻¹ ∈ W) :
    (⁅W, A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))⁆ :
      Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set L : Subgroup G := opPpPrimeCore G p with hL_def
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  set Lbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hLbar_def
  set Abar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := A.map mk
    with hAbar_def
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hker_mk : mk.ker = U := by rw [hmk_def, QuotientGroup.ker_mk', hU_eq_oPi]
  have hA_le_P : A ≤ (P : Subgroup G) := hA_mem.1
  have hA_pg : IsPGroup p A := hA_mem.2.1.isPGroup
  have hU_le_P : U ≤ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P
  -- `L = comap mk L̄`, and `L.map mk = L̄`.
  have hL_comap : L = Lbar.comap mk := by rw [hL_def, hLbar_def, hmk_def, opPpPrimeCore]
  have hLmap : L.map mk = Lbar := by rw [hL_def, hLbar_def, hmk_def]; exact opPpPrimeCore_map_eq_LBar
  have hU_le_L : U ≤ L := by rw [hU_eq_oPi, hL_def]; exact oPiCore_p_le_opPpPrimeCore
  -- `M = preimage of W`, `U ≤ M ≤ L`.
  set M : Subgroup G := W.comap mk with hM_def
  have hU_le_M : U ≤ M := by
    rw [hM_def, ← hker_mk]; intro x hx; rw [Subgroup.mem_comap, hx]; exact W.one_mem
  have hM_le_L : M ≤ L := by rw [hM_def, hL_comap]; exact Subgroup.comap_mono hW_le
  have hMmap : M.map mk = W := by
    rw [hM_def]; exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) W
  -- `H = M ⊔ A`.  `U ⊔ A ≤ H`, `P ≤ H`, `mk H = W ⊔ Abar`.
  set H : Subgroup G := M ⊔ A with hH_def
  have hUA_le_H : U ⊔ A ≤ H := sup_le_sup_right hU_le_M A
  have hP_le_H : (P : Subgroup G) ≤ H := by rw [← h_P_eq_UA]; exact hUA_le_H
  have hHmap : H.map mk = W ⊔ Abar := by
    rw [hH_def, Subgroup.map_sup, hMmap, hAbar_def]
  -- `Abar` normalizes `W` (from `hW_normalized`).
  have hAbar_inf_Lbar : Abar ⊓ Lbar = ⊥ := by
    rw [hAbar_def, hLbar_def]; exact AbarInf_LBar_eq_bot hA_pg
  have hAbar_norm_W : Abar ≤ Subgroup.normalizer (W : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw; exact hW_normalized a ha w hw
    · intro hw
      have := hW_normalized a⁻¹ (A.inv_mem ha) _ hw
      simpa [map_inv, mul_assoc] using this
  -- `H ≠ ⊤`: else `W ⊔ Abar = ⊤`, modular law forces `W = L̄`.
  have hH_ne_top : H ≠ ⊤ := by
    intro hHtop
    apply hW_ne
    have hWAbar_top : W ⊔ Abar = ⊤ := by rw [← hHmap, hHtop, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
    -- `(W ⊔ Abar) ⊓ L̄ = W` (modular law), and LHS `= ⊤ ⊓ L̄ = L̄`.
    have hmod := inf_sup_eq_of_le_normalizer_of_inf_eq_bot hW_le hAbar_inf_Lbar hAbar_norm_W
    rw [hWAbar_top, top_inf_eq] at hmod
    exact hmod.symm
  -- `P = UA ⊆ H` is a Sylow `p`-subgroup of `G` contained in `H`, hence Sylow in `↥H`
  -- (`Sylow.subtype`).  Since `P ⊆ H`, `H ⊓ P = P`, giving the form Step 3 wants.
  let S : Sylow p ↥H := P.subtype hP_le_H
  have hS_coe : (S : Subgroup ↥H) = (P : Subgroup G).subgroupOf H := P.coe_subtype hP_le_H
  have hHP_eq_P : H ⊓ (P : Subgroup G) = (P : Subgroup G) := inf_eq_right.mpr hP_le_H
  have hS_eq_HP : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H := by
    rw [hS_coe, hHP_eq_P]
  -- Step 3 applied to `H`: `⁅L ⊓ H, A⁆ ≤ U`.
  have hStep3 : (⁅L ⊓ H, A⁆ : Subgroup G) ≤ U :=
    step3_Abar_centralizes_inter_LBar P hp2 h_pSolvable h2abelian h_oPiPrime_trivial
      h_centralizer_center ih hA_mem hH_ne_top hUA_le_H S hS_eq_HP
  -- `M ≤ L ⊓ H`, so `⁅M, A⁆ ≤ ⁅L ⊓ H, A⁆ ≤ U = ker mk`.
  have hM_le_LinfH : M ≤ L ⊓ H := le_inf hM_le_L le_sup_left
  have hMA_le_U : (⁅M, A⁆ : Subgroup G) ≤ U :=
    (Subgroup.commutator_mono hM_le_LinfH le_rfl).trans hStep3
  -- `⁅W, Abar⁆ = mk⁅M, A⁆ ≤ mk U = ⊥`.
  have hcomm_map : (⁅M, A⁆ : Subgroup G).map mk = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker_mk]; exact hMA_le_U
  rw [← hMmap, hAbar_def, ← Subgroup.map_commutator, hcomm_map]

/-- The conjugation `MulDistribMulAction` of `↥Q` on the normal subgroup `↥N`
of `K`, via `MulAut.conjNormal ∘ Q.subtype`.  Under this action,
`a • n = ⟨↑a * ↑n * (↑a)⁻¹⟩`.  Used in Step 5 with `Q = Ā`, `N = L̄`. -/
private noncomputable def subgroupConjActionOnNormal
    {K : Type*} [Group K] (Q N : Subgroup K) [N.Normal] :
    MulDistribMulAction ↥Q ↥N :=
  MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp Q.subtype)

/-- **Isaacs Thm 7.6 Step 5** (mmd L3874): `|Ā| = p`, equivalently
`(O_p(G)).relIndex A = p`.

Given Step 4's output `P = UA` plus the running hypotheses and the induction
hypothesis, `Ā = A.map mk'` acts faithfully and coprimely on `L̄ = O_{p'}(Ḡ)`
(faithful by Step 1(c) + `Ā ⊓ L̄ = ⊥`; coprime by `p` vs `p'`).  By Lemma 6.20
(`isCyclic_of_faithful_trivial_on_proper_invariant`), `Ā` is cyclic — the
"trivial on every `Ā`-invariant proper subgroup `M̄ < L̄`" hypothesis is exactly
`step5_Abar_centralizes_invariant_proper` (Step 3 applied to `H = MA`).  A
nontrivial cyclic elementary abelian `p`-group has order `p`; the conversion of
`Nat.card Ā = p` to `(O_p(G)).relIndex A = p` is `relIndex_sup_of_inf_eq_bot`. -/
private theorem step5_Abar_card_eq_p.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (ih : ∀ (H : Type u) [Group H] [Finite H]
      [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H],
      Nat.card H < Nat.card G →
      (∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ →
      ∀ (Q : Sylow p H),
        Subgroup.centralizer
            (((Subgroup.center (Q : Subgroup H)).map
              (Q : Subgroup H).subtype) : Set H)
          = (Q : Subgroup H) →
        (Subgroup.thompsonJ (Q : Subgroup H) p).Normal)
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch01.opCore p G)
    (h_P_eq_UA : OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G)) :
    (OddOrder.Isaacs.Ch01.opCore p G).relIndex A = p := by
  classical
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G := h_pSolvable
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  set Lbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hLbar_def
  set Abar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := A.map mk
    with hAbar_def
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hA_pg : IsPGroup p A := hA_mem.2.1.isPGroup
  haveI hLbar_normal : Lbar.Normal := by
    rw [hLbar_def]; exact OddOrder.Isaacs.Ch03.oPiCore.normal _ _
  -- `Ā ⊓ L̄ = ⊥`, `Ā ≠ ⊥`.
  have hAbar_inf_Lbar : Abar ⊓ Lbar = ⊥ := by
    rw [hAbar_def, hLbar_def]; exact AbarInf_LBar_eq_bot hA_pg
  have hAbar_ne_bot : Abar ≠ ⊥ := by
    rw [hAbar_def, hmk_def]
    exact Abar_ne_bot_of_not_le (by rwa [hU_eq_oPi] at hA_not_le)
  -- The conjugation action `↥Ā ↷ ↥L̄`.  `a • n = ⟨↑a * ↑n * (↑a)⁻¹⟩`.
  letI : MulDistribMulAction ↥Abar ↥Lbar := subgroupConjActionOnNormal Abar Lbar
  have hsmul_coe : ∀ (a : ↥Abar) (n : ↥Lbar),
      ((a • n : ↥Lbar) : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) =
        (↑a : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) * ↑n * (↑a)⁻¹ := by
    intro a n; rfl
  -- `Ā` is elementary abelian (image of the elementary abelian `A`).
  have hAbar_el : OddOrder.GroupTheory.IsElementaryAbelian p ↥Abar := by
    rw [hAbar_def]
    exact isElementaryAbelian_map_of_isElementaryAbelian mk
      (A := A) ⟨hA_mem.2.1.1, hA_mem.2.1.2⟩
  -- `↥Ā` is abelian.
  haveI : IsMulCommutative ↥Abar := ⟨⟨hAbar_el.1⟩⟩
  -- The action is faithful: `a` fixes all of `L̄` ⇒ `↑a ∈ C_Ḡ(L̄)`, and `Ā ⊓ C_Ḡ(L̄) = ⊥`.
  have hAbar_inf_cent :
      Abar ⊓ Subgroup.centralizer
        (Lbar : Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
    rw [hAbar_def, hLbar_def]; exact AbarInf_centralizer_LBar_eq_bot hA_pg
  haveI : FaithfulSMul ↥Abar ↥Lbar := by
    refine ⟨fun {a b} h => ?_⟩
    -- `↑b⁻¹ * ↑a` centralizes `L̄`.
    set ga : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := a.1 with hga
    set gb : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := b.1 with hgb
    have hcent : gb⁻¹ * ga ∈ Subgroup.centralizer
        (Lbar : Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have heq := h ⟨m, hm⟩
      rw [Subtype.ext_iff, hsmul_coe, hsmul_coe, ← hga, ← hgb] at heq
      -- `heq : ga * m * ga⁻¹ = gb * m * gb⁻¹`  ⇒  `m * (gb⁻¹ * ga) = (gb⁻¹ * ga) * m`.
      calc m * (gb⁻¹ * ga)
          = gb⁻¹ * (gb * m * gb⁻¹) * ga := by group
        _ = gb⁻¹ * (ga * m * ga⁻¹) * ga := by rw [heq]
        _ = (gb⁻¹ * ga) * m := by group
    have hmem : gb⁻¹ * ga ∈ Abar ⊓ Subgroup.centralizer
        (Lbar : Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) :=
      ⟨Abar.mul_mem (Abar.inv_mem b.2) a.2, hcent⟩
    rw [hAbar_inf_cent, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem).symm
  -- Coprimality: `|Ā|` is a `p`-power, `|L̄|` is a `p'`-number.
  have hCop : Nat.Coprime (Nat.card ↥Abar) (Nat.card ↥Lbar) := by
    have hAbar_pg : IsPGroup p ↥Abar := by rw [hAbar_def]; exact hA_pg.map mk
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAbar_pg
    rw [hk]
    refine Nat.Coprime.pow_left k ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr ?_)
    intro hdvd
    have hLbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} Lbar := by
      rw [hLbar_def]; exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup
        (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) {q | q ≠ p}
    exact (hLbar_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
  -- `hproper`: `Ā` acts trivially on every `Ā`-invariant proper `M̄ < L̄`.
  have hproper : ∀ M : Subgroup ↥Lbar, (∀ a : ↥Abar, ∀ n ∈ M, a • n ∈ M) → M ≠ ⊤ →
      ∀ a : ↥Abar, ∀ n ∈ M, a • n = n := by
    intro M hM_inv hM_ne_top a n hn
    -- Set `W = M.map L̄.subtype ≤ L̄`, proper, `Ā`-invariant; apply the focused lemma.
    set W : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := M.map Lbar.subtype
      with hW_def
    have hW_le : W ≤ Lbar := by rw [hW_def]; exact Subgroup.map_subtype_le M
    have hW_ne : W ≠ Lbar := by
      intro hWtop
      apply hM_ne_top
      apply Subgroup.map_injective Lbar.subtype_injective
      rw [← hW_def, hWtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hW_normalized : ∀ a : G, a ∈ A → ∀ w, w ∈ W → mk a * w * (mk a)⁻¹ ∈ W := by
      intro g hg w hw
      obtain ⟨⟨w, hwL⟩, hwM, rfl⟩ := hw
      have hg_Abar : mk g ∈ Abar := Subgroup.mem_map_of_mem mk hg
      have hmoved := hM_inv ⟨mk g, hg_Abar⟩ ⟨w, hwL⟩ hwM
      rw [hW_def]
      have hsmul := hsmul_coe ⟨mk g, hg_Abar⟩ ⟨w, hwL⟩
      exact ⟨_, hmoved, hsmul⟩
    have hcomm := step5_Abar_centralizes_invariant_proper P hp2 h_pSolvable h2abelian
      h_oPiPrime_trivial h_centralizer_center ih hA_mem h_P_eq_UA hW_le hW_ne hW_normalized
    -- `⁅W, Ā⁆ = ⊥` ⇒ `Ā` centralizes `W` ⇒ `a • n = n`.
    apply Subtype.ext
    rw [hsmul_coe a n]
    -- `ga` and `gn` commute since `⁅W, Ā⁆ = ⊥` and `gn ∈ W`, `ga ∈ Ā`.
    set ga : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := a.1 with hga
    set gn : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := n.1 with hgn
    have hn_W : gn ∈ W := ⟨n, hn, rfl⟩
    have hcomm_mem : ⁅gn, ga⁆ ∈ (⊥ :
        Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator hn_W a.2
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hcomm_mem
    -- `gn` and `ga` commute ⇒ `ga * gn * ga⁻¹ = gn`.
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm_mem.symm.eq
  -- Apply Lemma 6.20: `Ā` is cyclic.
  have hAbar_cyclic : IsCyclic ↥Abar :=
    OddOrder.Isaacs.Ch06.isCyclic_of_faithful_trivial_on_proper_invariant hCop hproper
  -- `Ā` is nontrivial, elementary abelian, cyclic `p`-group ⇒ `|Ā| = p`.
  haveI : Nontrivial ↥Abar := (Subgroup.nontrivial_iff_ne_bot _).mpr hAbar_ne_bot
  have hAbar_card : Nat.card ↥Abar = p :=
    card_eq_prime_of_isElementaryAbelian_isCyclic_nontrivial hAbar_el hAbar_cyclic
  -- Convert `Nat.card Ā = p` to `U.relIndex A = p` via `relIndex_map_map` + diamond.
  -- `U.relIndex A = |A : A ⊓ U| = |Ā| = p` (`Ā = A.map mk ≅ A / (A ⊓ U)`, `ker mk = U`).
  rw [← hAbar_card]
  -- `U.relIndex A = (U.subgroupOf A).index`; `U.subgroupOf A = ker (mk ∘ A.subtype)`.
  change (U.subgroupOf A).index = Nat.card ↥Abar
  have hker : U.subgroupOf A = (mk.comp A.subtype).ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      hmk_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hU_eq_oPi]
  rw [hker]
  -- `|A : ker φ| = |range φ| = |A.map mk| = |Ā|` for `φ = mk ∘ A.subtype`.
  have hrange : (mk.comp A.subtype).range = Abar := by
    rw [hAbar_def, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact Subgroup.index_ker (mk.comp A.subtype)

/-- **Isaacs Thm 7.6 Steps 4 + 5** (mmd L3870-3878).

Together Steps 4-5 produce `P = UA ∧ A.relIndex U = p` given:
* The full Thm 7.6 hypotheses (i)-(v) on the running `G`.
* An induction hypothesis: Thm 7.6 holds for all proper subgroups `H < G`.
* A chosen `A ∈ E(P)` with `A ⊄ U` (Step 2 extraction).

**Step 4** (`P = UA`) is proved here as actual theorem code, using the focused
Step 3 axiom (`step3_Abar_centralizes_inter_LBar`).  **Step 5** (`|Ā| = p`)
is delegated to the focused `step5_Abar_card_eq_p` axiom.

Step 3 is **internal to this axiom**: both Step 4 and Step 5 use Step 3 by
applying the IH to proper subgroups (`H = LA` for Step 4, `H = MA` for any
Ā-invariant proper `M̄ < L̄` for Step 5).

The "|A : A ⊓ U|" formulation (= `A.relIndex U`) is used because the landed
Step 7 lemma (`omega1ZCenterOpCore_relIndex_inter_A_le`) consumes it directly. -/
private theorem step4_5_normal_J_hypotheses.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (ih : ∀ (H : Type u) [Group H] [Finite H]
      [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H],
      Nat.card H < Nat.card G →
      (∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ →
      ∀ (Q : Sylow p H),
        Subgroup.centralizer
            (((Subgroup.center (Q : Subgroup H)).map
              (Q : Subgroup H).subtype) : Set H)
          = (Q : Subgroup H) →
        (Subgroup.thompsonJ (Q : Subgroup H) p).Normal)
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G) ∧
      (OddOrder.Isaacs.Ch01.opCore p G).relIndex A = p := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set L : Subgroup G := opPpPrimeCore G p with hL_def
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  -- `U = O_{{p}}(G)` (kernel of `mk`), and `U ≤ L`.
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hker_mk : mk.ker = U := by rw [hmk_def, QuotientGroup.ker_mk', hU_eq_oPi]
  have hU_le_L : U ≤ L := by
    rw [hU_eq_oPi, hL_def]; exact oPiCore_p_le_opPpPrimeCore
  -- Basic facts about `A` and `U`.
  have hA_le_P : A ≤ (P : Subgroup G) := hA_mem.1
  have hA_pg : IsPGroup p A := hA_mem.2.1.isPGroup
  have hU_le_P : U ≤ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P
  -- `UA = U ⊔ A`, `LA = L ⊔ A`.
  set UA : Subgroup G := U ⊔ A with hUA_def
  set LA : Subgroup G := L ⊔ A with hLA_def
  have hUA_le_P : UA ≤ (P : Subgroup G) := sup_le hU_le_P hA_le_P
  have hUA_le_LA : UA ≤ LA := sup_le_sup_right hU_le_L A
  have hUA_pg : IsPGroup p ↥UA :=
    P.isPGroup'.of_injective (Subgroup.inclusion hUA_le_P)
      (Subgroup.inclusion_injective hUA_le_P)
  -- `Ā = A.map mk`, `L̄ = L.map mk = O_{p'}(Ḡ)`.
  set Abar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := A.map mk
    with hAbar_def
  set Lbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := L.map mk
    with hLbar_def
  have hLbar_eq : Lbar = OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
    rw [hLbar_def, hL_def, hmk_def]; exact opPpPrimeCore_map_eq_LBar
  haveI : Lbar.Normal := by rw [hLbar_eq]; exact OddOrder.Isaacs.Ch03.oPiCore.normal _ _
  -- `Ā ⊓ L̄ = ⊥` (p-group vs p'-group) and `Ā ≠ ⊥`.
  have hAbar_inf_Lbar : Abar ⊓ Lbar = ⊥ := by
    rw [hAbar_def, hLbar_eq]; exact AbarInf_LBar_eq_bot hA_pg
  have hAbar_ne_bot : Abar ≠ ⊥ := by
    rw [hAbar_def, hmk_def]
    exact Abar_ne_bot_of_not_le (by rwa [hU_eq_oPi] at hA_not_le)
  -- Step 4: prove `LA = ⊤`, then `UA = P`.
  have hLA_top : LA = ⊤ := by
    by_contra hLA_ne_top
    -- Build the Sylow `p`-subgroup `UA.subgroupOf LA` of `↥LA`.
    have hUA_le_LA' : UA ≤ LA := hUA_le_LA
    have hL_le_LA : L ≤ LA := le_sup_left
    have hA_le_LA : A ≤ LA := le_sup_right
    -- `UA.subgroupOf LA` is a `p`-group.
    have hUAsub_pg : IsPGroup p ↥(UA.subgroupOf LA) := hUA_pg.comap_subtype
    -- Its index in `↥LA` is `UA.relIndex LA = Nat.card L̄`, a `p'`-number.
    have hidx_eq : (UA.subgroupOf LA).index = UA.relIndex LA := rfl
    -- `UA.relIndex LA = Nat.card Lbar` via `relIndex_map_map` + diamond.
    have hrelindex_map : (Abar).relIndex (Lbar ⊔ Abar) = UA.relIndex LA := by
      rw [hAbar_def, hLbar_def]
      rw [← Subgroup.map_sup]
      rw [Subgroup.relIndex_map_map mk A (L ⊔ A)]
      rw [hker_mk]
      -- `(A ⊔ U).relIndex ((L ⊔ A) ⊔ U) = UA.relIndex LA` since `U ≤ A⊔U`, `U ≤ LA`.
      congr 1
      · rw [hUA_def, sup_comm]
      · rw [hLA_def]; rw [sup_assoc, sup_comm A U, ← sup_assoc, sup_eq_left.mpr hU_le_L]
    have hAbar_relindex : (Abar).relIndex (Lbar ⊔ Abar) = Nat.card Lbar :=
      relIndex_sup_of_inf_eq_bot (by rw [inf_comm]; exact hAbar_inf_Lbar)
    have hUA_relindex_LA : UA.relIndex LA = Nat.card Lbar := by
      rw [← hrelindex_map, hAbar_relindex]
    -- `Nat.card Lbar` is a `p'`-number, so `p ∤ (UA.subgroupOf LA).index`.
    have hLbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} Lbar := by
      rw [hLbar_eq]; exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) {q | q ≠ p}
    have hp_not_dvd : ¬ p ∣ (UA.subgroupOf LA).index := by
      rw [hidx_eq, hUA_relindex_LA]
      intro hdvd
      exact (hLbar_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
    -- The Sylow subgroup `S`.
    let S : Sylow p ↥LA := hUAsub_pg.toSylow hp_not_dvd
    have hS_coe : (S : Subgroup ↥LA) = UA.subgroupOf LA := hUAsub_pg.toSylow_coe hp_not_dvd
    -- `S = (LA ⊓ P).subgroupOf LA`: both are `p`-subgroups, `S` Sylow, `S ≤ (LA⊓P)sub`.
    have hLAP_pg : IsPGroup p ↥((LA ⊓ (P : Subgroup G)).subgroupOf LA) := by
      have : IsPGroup p ↥(LA ⊓ (P : Subgroup G)) :=
        P.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
          (Subgroup.inclusion_injective _)
      exact this.comap_subtype
    have hS_le_LAP : (S : Subgroup ↥LA) ≤ (LA ⊓ (P : Subgroup G)).subgroupOf LA := by
      rw [hS_coe]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨x.property, hUA_le_P hx⟩
    have hS_eq_LAP : ((LA ⊓ (P : Subgroup G)).subgroupOf LA) = (S : Subgroup ↥LA) :=
      S.is_maximal' hLAP_pg hS_le_LAP
    -- Apply Step 3 with `H = LA`: `⁅L ⊓ LA, A⁆ ≤ U`.
    have hUA_le_H : U ⊔ A ≤ LA := sup_le (hU_le_L.trans hL_le_LA) hA_le_LA
    have hStep3 : (⁅L ⊓ LA, A⁆ : Subgroup G) ≤ U :=
      step3_Abar_centralizes_inter_LBar P hp2 h_pSolvable h2abelian h_oPiPrime_trivial
        h_centralizer_center ih hA_mem hLA_ne_top hUA_le_H S hS_eq_LAP.symm
    -- `L ⊓ LA = L` (since `L ≤ LA`).
    have hL_inf_LA : L ⊓ LA = L := inf_eq_left.mpr hL_le_LA
    rw [hL_inf_LA] at hStep3
    -- `⁅L, A⁆ ≤ U = ker mk` ⇒ `⁅L̄, Ā⁆ = ⊥` ⇒ `Ā ≤ C_Ḡ(L̄)`.
    have hcomm_map : (⁅L, A⁆ : Subgroup G).map mk = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hker_mk]; exact hStep3
    have hAbar_le_cent : Abar ≤ Subgroup.centralizer (Lbar : Set _) := by
      rw [hAbar_def, hLbar_def, ← Subgroup.commutator_eq_bot_iff_le_centralizer,
        ← Subgroup.map_commutator]
      rw [Subgroup.commutator_comm]
      exact hcomm_map
    -- Step 1(c): `C_Ḡ(L̄) ≤ L̄`.
    have hcent_le_Lbar : Subgroup.centralizer (Lbar : Set _) ≤ Lbar := by
      rw [hLbar_eq]; exact step1_c_centralizer_oPiPrime_quotient_le_self
    -- So `Ā ≤ L̄`, hence `Ā = Ā ⊓ L̄ = ⊥`, contradiction.
    have hAbar_le_Lbar : Abar ≤ Lbar := hAbar_le_cent.trans hcent_le_Lbar
    have hAbar_bot : Abar = ⊥ := by
      rw [← inf_eq_left.mpr hAbar_le_Lbar]; exact hAbar_inf_Lbar
    exact hAbar_ne_bot hAbar_bot
  -- From `LA = ⊤`: `UA = LA ⊓ P = ⊤ ⊓ P = P`.  Use `UA = LA ⊓ P`.
  have hUA_eq_P : UA = (P : Subgroup G) := by
    -- We re-derive the Sylow identity at `H = LA = ⊤`: `UA.subgroupOf LA = (LA⊓P).subgroupOf LA`,
    -- then map back.  With `LA = ⊤`, `LA ⊓ P = P`.
    apply le_antisymm hUA_le_P
    -- `P ≤ UA`: since `LA = ⊤`, `P ≤ LA`, and `LA ⊓ P = P` is a `p`-subgroup of `↥LA`
    -- containing the Sylow `UA.subgroupOf LA`, forcing equality.
    have hP_le_LA : (P : Subgroup G) ≤ LA := by rw [hLA_top]; exact le_top
    have hUAsub_pg : IsPGroup p ↥(UA.subgroupOf LA) := hUA_pg.comap_subtype
    have hidx_eq : (UA.subgroupOf LA).index = UA.relIndex LA := rfl
    have hrelindex_map : (Abar).relIndex (Lbar ⊔ Abar) = UA.relIndex LA := by
      rw [hAbar_def, hLbar_def, ← Subgroup.map_sup, Subgroup.relIndex_map_map mk A (L ⊔ A),
        hker_mk]
      congr 1
      · rw [hUA_def, sup_comm]
      · rw [hLA_def, sup_assoc, sup_comm A U, ← sup_assoc, sup_eq_left.mpr hU_le_L]
    have hAbar_relindex : (Abar).relIndex (Lbar ⊔ Abar) = Nat.card Lbar :=
      relIndex_sup_of_inf_eq_bot (by rw [inf_comm]; exact hAbar_inf_Lbar)
    have hLbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} Lbar := by
      rw [hLbar_eq]; exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) {q | q ≠ p}
    have hp_not_dvd : ¬ p ∣ (UA.subgroupOf LA).index := by
      rw [hidx_eq, hrelindex_map.symm.trans hAbar_relindex]
      intro hdvd
      exact (hLbar_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
    let S : Sylow p ↥LA := hUAsub_pg.toSylow hp_not_dvd
    have hS_coe : (S : Subgroup ↥LA) = UA.subgroupOf LA := hUAsub_pg.toSylow_coe hp_not_dvd
    have hLAP_pg : IsPGroup p ↥((LA ⊓ (P : Subgroup G)).subgroupOf LA) := by
      have : IsPGroup p ↥(LA ⊓ (P : Subgroup G)) :=
        P.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
          (Subgroup.inclusion_injective _)
      exact this.comap_subtype
    have hS_le_LAP : (S : Subgroup ↥LA) ≤ (LA ⊓ (P : Subgroup G)).subgroupOf LA := by
      rw [hS_coe]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨x.property, hUA_le_P hx⟩
    have hS_eq_LAP : ((LA ⊓ (P : Subgroup G)).subgroupOf LA) = (S : Subgroup ↥LA) :=
      S.is_maximal' hLAP_pg hS_le_LAP
    -- So `(LA⊓P).subgroupOf LA = UA.subgroupOf LA`, hence `LA ⊓ P = UA` (both ≤ LA).
    rw [hS_coe] at hS_eq_LAP
    have hLAP_eq_UA : LA ⊓ (P : Subgroup G) = UA := by
      have hmap := congrArg (fun K : Subgroup ↥LA => K.map LA.subtype) hS_eq_LAP
      simp only [Subgroup.subgroupOf, Subgroup.map_comap_eq, LA.range_subtype] at hmap
      rwa [inf_eq_right.mpr (inf_le_left), inf_eq_right.mpr hUA_le_LA] at hmap
    -- `P ≤ LA ⊓ P = UA`.
    intro x hxP
    rw [← hLAP_eq_UA]
    exact ⟨hP_le_LA hxP, hxP⟩
  refine ⟨hUA_eq_P, ?_⟩
  -- Step 5 (delegated): `U.relIndex A = p`.
  exact step5_Abar_card_eq_p P hp2 h_pSolvable h2abelian h_oPiPrime_trivial
    h_centralizer_center ih hA_mem hA_not_le hUA_eq_P

/-! ### Step 8 action setup: `Ḡ →* MulAut V` (mmd L3879)

The book's Step 8 builds the conjugation action `Ḡ ↷ V` and checks
faithfulness (Step 6).  Below we lift `MulAut.conjNormal : G →* MulAut V` to a
homomorphism `Ḡ →* MulAut V` via `QuotientGroup.lift`, using `U ≤ ker` (which
holds because `V ⊆ Z(U)`). -/

/-- `O_p(G) ≤ ker (MulAut.conjNormal : G →* MulAut V)`: every `u ∈ U`
centralizes `V = Ω₁ Z(U)` (since `V ⊆ Z(U)`). -/
private theorem opCore_le_ker_conjNormal_omega1ZCenterOpCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    OddOrder.Isaacs.Ch01.opCore p G ≤
      (MulAut.conjNormal (H := omega1ZCenterOpCore G p)).ker := by
  intro u hu_U
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro v
  -- Goal: (MulAut.conjNormal u) v = (1 : MulAut V) v = v
  apply Subtype.ext
  -- Goal: ↑((MulAut.conjNormal u) v) = ↑v
  rw [MulAut.conjNormal_apply]
  -- Goal: u * v * u⁻¹ = v
  have hv_cent : (v : G) ∈ Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) :=
    omega1ZCenterOpCore_centralizes_opCore v.property
  have hvu : (u : G) * (v : G) = (v : G) * (u : G) :=
    (Subgroup.mem_centralizer_iff.mp hv_cent) u hu_U
  -- Convert "(1 : MulAut V) v" on the RHS.
  change (u : G) * (v : G) * (u : G)⁻¹ = (v : G)
  calc (u : G) * (v : G) * (u : G)⁻¹
      = (v : G) * (u : G) * (u : G)⁻¹ := by rw [hvu]
    _ = (v : G) := by group

/-- **The factored action `Ḡ →* MulAut V`**: lifts `MulAut.conjNormal` via
`U ≤ ker`. -/
private noncomputable def conjActionOnOmega1ZCenter_quotient
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) →*
      MulAut ↥(omega1ZCenterOpCore G p) :=
  QuotientGroup.lift _ MulAut.conjNormal (by
    rw [show OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G =
        OddOrder.Isaacs.Ch01.opCore p G from
      OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p]
    exact opCore_le_ker_conjNormal_omega1ZCenterOpCore)

/-- The kernel of `MulAut.conjNormal : G →* MulAut V` (for a normal subgroup `V`)
is exactly `C_G(V)`: `g` acts trivially on `V` iff `g` centralizes `V`. -/
private theorem conjNormal_ker_eq_centralizer
    {G : Type*} [Group G] {V : Subgroup G} [V.Normal] :
    (MulAut.conjNormal (H := V)).ker = Subgroup.centralizer (V : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg v hv
    -- `conjNormal g = 1` ⇒ `g * v * g⁻¹ = v`, i.e. `g * v = v * g`.
    have hfix : (MulAut.conjNormal g (⟨v, hv⟩ : V) : G) = ((⟨v, hv⟩ : V) : G) := by
      rw [hg]; rfl
    rw [MulAut.conjNormal_apply] at hfix
    -- `g * v * g⁻¹ = v` ⇒ `g * v = v * g`.
    have : g * v * g⁻¹ * g = v * g := by rw [hfix]
    have hcomm : g * v = v * g := by simpa [mul_assoc] using this
    exact hcomm.symm
  · intro hg
    -- Every `v ∈ V` is fixed: `g * v * g⁻¹ = v`.
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    simp only [MulAut.one_apply]
    rw [MulAut.conjNormal_apply]
    have hcomm : (v : G) * g = g * (v : G) := hg (v : G) v.property
    -- `g * v * g⁻¹ = v * g * g⁻¹ = v`.
    rw [← hcomm]; group

/-- **Isaacs Thm 7.6 Step 8a** (local axiom — mmd L3893-3895): apply Thm 7.5.

Given Step 4-5-6-7 outputs:
* `P = UA` (Step 4)
* `|Ā| = p` (Step 5)
* The Ḡ-action on V is faithful (= Step 6, landed via
  `centralizer_omega1ZCenterOpCore_map_eq_bot_of_le_opCore`)
* `|V : V ∩ A| ≤ p` (Step 7, landed via `omega1ZCenterOpCore_relIndex_inter_A_le`)
plus the running Thm 7.6 hypotheses (i)-(v),

apply Thm 7.5 (`sylow_normal_of_elementary_normal_P_theorem`) to derive
`P̄ ⊴ Ḡ`. -/
private theorem step8a_PBar_normal_GBar
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (_h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (_h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (_h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (h_P_eq_UA : OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G))
    (_h_Abar_card_eq_p :
       (OddOrder.Isaacs.Ch01.opCore p G).relIndex A = p)
    (h_V_inter_A_le_p : A.relIndex (omega1ZCenterOpCore G p) ≤ p)
    (h_K_map_eq_bot :
       (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).map
         (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥) :
    ((P : Subgroup G).map
      (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))).Normal := by
  classical
  -- Abbreviations: `U = O_p(G) = O_{{p}}(G)`, `Ḡ = G/U`, `V = Ω₁(Z(U))`,
  -- `φ : Ḡ →* MulAut V` the lifted conjugation action.
  set U : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G with hU_def
  set mk : G →* G ⧸ U := QuotientGroup.mk' U with hmk_def
  set V : Subgroup G := omega1ZCenterOpCore G p with hV_def
  set φ : (G ⧸ U) →* MulAut ↥V := conjActionOnOmega1ZCenter_quotient G p with hφ_def
  -- `U = O_p(G)` definitionally.
  have hU_eq : U = OddOrder.Isaacs.Ch01.opCore p G :=
    OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p
  -- (Hypothesis 1) `Ḡ` is `p`-separable: instance from `quotient_isPiSeparable`.
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) (G ⧸ U) := inferInstance
  -- (Hypothesis 3) Every `2`-subgroup of `Ḡ` is abelian, by `quotient_two_subgroup_abelian`.
  have h2abelian_bar :
      ∀ S : Subgroup (G ⧸ U), IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x :=
    fun S hS2 => quotient_two_subgroup_abelian h2abelian S hS2
  -- (Hypothesis 4) `φ` is faithful: `ker φ = C_G(V).map mk = ⊥`.
  have hφ_inj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    -- `ker φ = (conjNormal).ker.map mk = C_G(V).map mk`.
    have hker : φ.ker = (Subgroup.centralizer (V : Set G)).map mk := by
      rw [hφ_def, hmk_def]
      unfold conjActionOnOmega1ZCenter_quotient
      rw [QuotientGroup.ker_lift, conjNormal_ker_eq_centralizer]
    rw [hker]
    exact h_K_map_eq_bot
  -- (Hypothesis 5 ingredient) `V` is a `p`-group.
  have hV_pg : IsPGroup p ↥V := omega1ZCenterOpCore_isPGroup p
  -- The candidate normal Sylow `P̄ = P.map mk` as a `Sylow p Ḡ`.
  set PBar : Sylow p (G ⧸ U) := P.mapSurjective (QuotientGroup.mk'_surjective U) with hPBar_def
  have hPBar_coe : (PBar : Subgroup (G ⧸ U)) = (P : Subgroup G).map mk := by
    rw [hPBar_def, Sylow.coe_mapSurjective]
  -- `P̄ = Ā` since `Ū = ⊥` and `P = UA`.
  have hPBar_eq_Abar : (PBar : Subgroup (G ⧸ U)) = A.map mk := by
    rw [hPBar_coe, ← h_P_eq_UA, ← hU_eq, Subgroup.map_sup]
    -- `U.map mk = ⊥`.
    have hU_map : U.map mk = ⊥ := by
      rw [hmk_def, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hU_map, bot_sup_eq]
  -- `A` is abelian (it is elementary abelian).
  have hA_comm : ∀ a b : ↥A, a * b = b * a := (hA_mem.2.1).comm
  -- Key step: `(actionCentralizer φ P̄).index ≤ p`, because `E = V ∩ A` is fixed by `P̄ = Ā`.
  -- Membership: every `v : ↥V` whose underlying element lies in `A` is `P̄`-fixed.
  have hE_le_centralizer :
      (A.subgroupOf V) ≤ actionCentralizer φ (PBar : Subgroup (G ⧸ U)) := by
    intro v hv
    -- `hv : (v : G) ∈ A` (membership of the subgroupOf).
    rw [Subgroup.mem_subgroupOf] at hv
    rw [mem_actionCentralizer]
    intro q
    -- `q ∈ P̄ = Ā`, so `q = mk a` for some `a ∈ A`.
    have hq_mem : (q : G ⧸ U) ∈ A.map mk := hPBar_eq_Abar ▸ q.property
    obtain ⟨a, ha_A, ha_eq⟩ := hq_mem
    -- `φ q v = φ (mk a) v = conjNormal a v = a * v * a⁻¹ = v` (A abelian).
    apply Subtype.ext
    have hφq : φ (q : G ⧸ U) = MulAut.conjNormal a := by
      rw [hφ_def]
      unfold conjActionOnOmega1ZCenter_quotient
      rw [← ha_eq, hmk_def]
      exact QuotientGroup.lift_mk' _ _ a
    rw [hφq, MulAut.conjNormal_apply]
    -- `a * v * a⁻¹ = v` since `a, v ∈ A` and `A` is abelian.
    have hcomm : a * (v : G) = (v : G) * a :=
      congrArg Subtype.val (hA_comm ⟨a, ha_A⟩ ⟨(v : G), hv⟩)
    rw [hcomm]; group
  -- `(actionCentralizer φ P̄).index ≤ (A.subgroupOf V).index = A.relIndex V ≤ p`.
  have hPBar_index : (actionCentralizer φ (PBar : Subgroup (G ⧸ U))).index ≤ p := by
    have h1 : (actionCentralizer φ (PBar : Subgroup (G ⧸ U))).index ≤
        (A.subgroupOf V).index := Subgroup.index_antitone hE_le_centralizer
    calc (actionCentralizer φ (PBar : Subgroup (G ⧸ U))).index
        ≤ (A.subgroupOf V).index := h1
      _ = A.relIndex V := rfl
      _ ≤ p := h_V_inter_A_le_p
  -- Extend the bound to *every* Sylow of `Ḡ` via conjugacy.
  have h_centralizer_index :
      ∀ R : Sylow p (G ⧸ U), (actionCentralizer φ (R : Subgroup (G ⧸ U))).index ≤ p := by
    intro R
    -- `R` and `P̄` are conjugate: `R = ḡ • P̄`.
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ U) PBar R
    have hR_eq : (R : Subgroup (G ⧸ U)) =
        (PBar : Subgroup (G ⧸ U)).map (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [hR_eq, actionCentralizer_map_conj_index]
    exact hPBar_index
  -- Apply Theorem 7.5 to `φ : Ḡ →* MulAut V` and the Sylow `P̄`.
  have hPBar_normal : (PBar : Subgroup (G ⧸ U)).Normal :=
    sylow_normal_of_elementary_normal_P_theorem hp2 h2abelian_bar hφ_inj hV_pg
      h_centralizer_index PBar
  -- Transport normality to `(P : Subgroup G).map mk`.
  rwa [hPBar_coe] at hPBar_normal

/-- **Isaacs Thm 7.6 Step 8b** (mmd L3896): pull back `P̄ ⊴ Ḡ` to derive `False`.

Once `P̄ ⊴ Ḡ` is established (Step 8a), correspondence-theorem reasoning gives
`P ⊴ G` (since `U ≤ P`, the preimage of `P̄` is `P`).  Then `P.Normal` and
`IsPGroup p P` give `P ≤ opCore p G = U` via `normal_pgroup_le_opCore`.
Combined with `A ≤ P`, this contradicts `A ⊄ U`. -/
theorem step8b_pullback_normal_P
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {A : Subgroup G}
    (hA_le_P : A ≤ (P : Subgroup G))
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch01.opCore p G)
    (hPBar_normal :
       ((P : Subgroup G).map
         (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))).Normal) :
    False := by
  -- (1) U ≤ P (general).
  have hU_le_P : OddOrder.Isaacs.Ch01.opCore p G ≤ (P : Subgroup G) :=
    OddOrder.Isaacs.Ch01.opCore_le P
  -- (2) U ≤ oPiCore_p (definitionally equal).
  have hU_eq : OddOrder.Isaacs.Ch01.opCore p G =
      OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  -- (3) (P.map mk').comap mk' = P (since U ≤ P, and U = kernel of mk').
  have hP_preimage :
      ((P : Subgroup G).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))).comap
          (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) =
        (P : Subgroup G) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    -- Goal: P ⊔ oPiCore {p} G = P. Use U ≤ P.
    rw [← hU_eq]
    exact sup_eq_left.mpr hU_le_P
  -- (4) P̄ ⊴ Ḡ ⇒ comap P̄ = P is normal in G.
  have hP_normal : (P : Subgroup G).Normal := by
    rw [← hP_preimage]
    exact hPBar_normal.comap (QuotientGroup.mk' _)
  -- (5) P is a normal p-group ⇒ P ≤ opCore p G = U.
  have hP_pg : IsPGroup p (P : Subgroup G) := P.isPGroup'
  haveI := hP_normal
  have hP_le_U : (P : Subgroup G) ≤ OddOrder.Isaacs.Ch01.opCore p G :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hP_pg
  -- (6) A ≤ P ≤ U contradicts hA_not_le.
  exact hA_not_le (hA_le_P.trans hP_le_U)

/-- **Isaacs Thm 7.6 Step 1-7 conclusion**: `J(P) ≤ O_p(G)`.

Proved by strong induction on `Nat.card G` (so Step 3 can use the IH on proper
subgroups) + Step 2 extraction (`thompsonJ_le_iff`) + the Step 4-5 axiom
(`step4_5_normal_J_hypotheses`) + the landed Step 6 (`...isPGroup` /
`...le_opCore_of_isPGroup` / `...map_eq_bot_of_le_opCore`) + the landed Step 7
(`omega1ZCenterOpCore_relIndex_inter_A_le`) + the Step 8 axiom
(`step8_normal_J_closure`). -/
theorem thompsonJ_le_opCore_of_normal_J_hypotheses
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  classical
  -- Strong induction on `Nat.card G`, with the motive parametrized over arbitrary
  -- groups whose order is less than `|G|` and which satisfy the descended hypotheses.
  let motive : ℕ → Prop := fun n =>
    ∀ (H : Type _) [Group H] [Finite H] [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H]
      (_h2abelian : ∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
      (_h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥)
      (Q : Sylow p H)
      (_h_centralizer_center :
         Subgroup.centralizer
           (((Subgroup.center (Q : Subgroup H)).map (Q : Subgroup H).subtype) : Set H)
           = (Q : Subgroup H)),
      Nat.card H = n → Subgroup.thompsonJ (Q : Subgroup H) p ≤ OddOrder.Isaacs.Ch01.opCore p H
  suffices hmain : motive (Nat.card G) by
    exact hmain G h2abelian h_oPiPrime_trivial P h_centralizer_center rfl
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih H _ _ _ h2abelian' h_oPiPrime_trivial' Q h_centralizer_center' hcard
  -- The induction hypothesis at the "normal_J" level (i.e., normality of J(Q')
  -- in H' for groups H' with order < n).
  have ih_normal :
      ∀ (H' : Type _) [Group H'] [Finite H']
        [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H'],
      Nat.card H' < Nat.card H →
      (∀ S : Subgroup H', IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H' = ⊥ →
      ∀ (Q' : Sylow p H'),
        Subgroup.centralizer
            (((Subgroup.center (Q' : Subgroup H')).map
              (Q' : Subgroup H').subtype) : Set H')
          = (Q' : Subgroup H') →
        (Subgroup.thompsonJ (Q' : Subgroup H') p).Normal := by
    intro H' _ _ _ hH'_lt h2abelian'' h_oPiPrime_trivial'' Q' h_centralizer_center''
    have hH'_lt_n : Nat.card H' < n := hH'_lt.trans_eq hcard
    have h_le_op' :=
      ih (Nat.card H') hH'_lt_n H' h2abelian'' h_oPiPrime_trivial'' Q' h_centralizer_center'' rfl
    exact normal_thompsonJ_of_le_opCore Q' h_le_op'
  -- Now prove `J(Q) ≤ U` on the running group `H` of order `n` using Step 2 extraction
  -- + the Steps 4-5 axiom + Step 6 (landed) + Step 7 (landed) + Step 8 closure axiom.
  haveI h_pSolvable_in_H : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H :=
    inferInstance
  rw [thompsonJ_le_iff]
  intro A hA_mem
  by_contra hA_not_le
  -- Package the induction hypothesis for use by the Step 4-5 axiom.
  have ih_for_axioms :
      ∀ (H' : Type _) [Group H'] [Finite H']
        [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H'],
      Nat.card H' < Nat.card H →
      (∀ S : Subgroup H', IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H' = ⊥ →
      ∀ (Q' : Sylow p H'),
        Subgroup.centralizer
            (((Subgroup.center (Q' : Subgroup H')).map
              (Q' : Subgroup H').subtype) : Set H')
          = (Q' : Subgroup H') →
        (Subgroup.thompsonJ (Q' : Subgroup H') p).Normal :=
    fun H' _ _ _ hH'_lt h2 h_oPi Q' h_cent =>
      ih_normal H' hH'_lt h2 h_oPi Q' h_cent
  -- (Step 4 + Step 5): `P = UA` and `A.relIndex U = p` (= `|Ā| = p`).
  obtain ⟨h_P_eq_UA, h_Abar_card_eq_p⟩ :=
    step4_5_normal_J_hypotheses (G := H) Q hp2 h_pSolvable_in_H h2abelian'
      h_oPiPrime_trivial' h_centralizer_center' ih_for_axioms hA_mem hA_not_le
  have hA_D_relIndex : (OddOrder.Isaacs.Ch01.opCore p H).relIndex A ≤ p :=
    le_of_eq h_Abar_card_eq_p
  -- (Step 7): `A.relIndex V ≤ p`, from the landed counting lemma.
  have hV_inter_A_le_p : A.relIndex (omega1ZCenterOpCore H p) ≤ p :=
    omega1ZCenterOpCore_relIndex_inter_A_le Q hA_mem hA_D_relIndex
  -- (Step 6): `K̄ = ⊥` from K = C_G(V) being a p-group (landed), hence K ≤ U.
  have h_K_pg : IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore H p : Set H)) :=
    centralizer_omega1ZCenterOpCore_isPGroup h_oPiPrime_trivial' Q h_centralizer_center'
  have h_K_le_U : Subgroup.centralizer (omega1ZCenterOpCore H p : Set H) ≤
      OddOrder.Isaacs.Ch01.opCore p H :=
    centralizer_omega1ZCenterOpCore_le_opCore_of_isPGroup h_K_pg
  have h_K_map_eq_bot :
      (Subgroup.centralizer (omega1ZCenterOpCore H p : Set H)).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) H)) = ⊥ :=
    centralizer_omega1ZCenterOpCore_map_eq_bot_of_le_opCore h_K_le_U
  -- (Step 8a): apply Thm 7.5 to get P̄ ⊴ Ḡ.
  have hPBar_normal :
      ((Q : Subgroup H).map (QuotientGroup.mk'
        (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) H))).Normal :=
    step8a_PBar_normal_GBar (G := H) Q hp2 h_pSolvable_in_H h2abelian'
      h_oPiPrime_trivial' h_centralizer_center' hA_mem h_P_eq_UA h_Abar_card_eq_p
      hV_inter_A_le_p h_K_map_eq_bot
  -- (Step 8b): pull back P̄ ⊴ Ḡ to derive `False` from `A ⊆ P ⊆ U`.
  exact step8b_pullback_normal_P Q hA_mem.1 hA_not_le hPBar_normal

/-- **Isaacs Thm 7.6** (normal-J theorem, unconditional).

The full theorem (Isaacs L3832) states:

> Suppose `G` is `p`-solvable with `p ≠ 2`, Sylow `2`-subgroups of `G` are abelian,
> `O_{p'}(G) = 1`, and `P = C_G(Z(P))` for some `P ∈ Syl_p(G)`.  Then `J(P) ⊴ G`.

The textbook proof (Isaacs p.209-214) is an **8-step Goldschmidt-style argument**:
Steps 1-7 establish `J(P) ≤ O_p(G)` using Thm 7.5 (normal-P), Ch.4 Cor 4.35
(`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`), Ch.6 Thm 6.20
(`isCyclic_of_faithful_trivial_on_proper_invariant`), and Hall-Higman 3.21.
Step 8 propagates normality from `O_p(G)` to `G` via Thm 7.2
(`thompsonJ_eq_of_le_of_le`) + characteristic-of-characteristic transport.

Remaining local axioms: `step4_5_normal_J_hypotheses` (Step 4+5 = `P = UA` and
`|Ā| = p`, both using Step 3's IH internally) and `step8_normal_J_closure`
(Step 8 = Thm 7.5 application + pullback).  All earlier landed bridge lemmas
(Steps 1, 6, 7) are unconditional. -/
theorem normal_J
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    (Subgroup.thompsonJ (P : Subgroup G) p).Normal := by
  have h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G :=
    thompsonJ_le_opCore_of_normal_J_hypotheses P hp2 h_pSolvable h2abelian
      h_oPiPrime_trivial h_centralizer_center
  exact normal_thompsonJ_of_le_opCore P h_le


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

/-- **Isaacs Lem 7.7 (a)** (image of normalizer under p'-quotient).

`N ⊴ G` で `p ∤ |N|`, `P` が `G` の非自明 `p`-部分群とすると, `f := mk' N` について
`N_Ḡ(P̄) = (N_G(P)).map f`.

This is exactly Isaacs Lemma 2.17 in the quotient form needed in Ch.7. -/
theorem normalizer_map_of_coprime_kernel [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_neBot : P ≠ ⊥) (hP_pgroup : IsPGroup p P) :
    Subgroup.normalizer
        ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.normalizer P).map (QuotientGroup.mk' N) :=
  OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel
    hp_coprime hP_neBot hP_pgroup

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
    {P : Subgroup G} (hP_neBot : P ≠ ⊥) (hP_pgroup : IsPGroup p P) :
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
  have hP_inf_N : P ⊓ N = ⊥ := Subgroup.inf_eq_bot_of_coprime h_coprime_PN
  -- ker f = N
  have hf_ker : f.ker = N := QuotientGroup.ker_mk' N
  refine le_antisymm ?_ ?_
  · -- ⊆ direction (hard)
    -- Cbar ≤ Nbar
    have hCbar_le_Nbar : Cbar ≤ Subgroup.normalizer Pbar := centralizer_le_normalizer Pbar
    -- Nbar = (N_G(P)).map f by Lem 2.17 (a)
    have hN_eq : Subgroup.normalizer Pbar = (Subgroup.normalizer P).map f := by
      rw [hPbar_def, hf_def]
      exact OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel hp_coprime hP_neBot hP_pgroup
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
        show f n ∈ Cbar
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
    {P : Subgroup G} (hP_neBot : P ≠ ⊥) (hP_pgroup : IsPGroup p P) :
    (Subgroup.normalizer
        ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.normalizer P).map (QuotientGroup.mk' N)) ∧
    (Subgroup.centralizer
        ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = (Subgroup.centralizer (P : Set G)).map (QuotientGroup.mk' N)) :=
  ⟨normalizer_map_of_coprime_kernel hp_coprime hP_neBot hP_pgroup,
    centralizer_map_of_coprime_kernel hp_coprime hP_neBot hP_pgroup⟩

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
    {P : Subgroup G} (hP_neBot : P ≠ ⊥) (hP_pgroup : IsPGroup p P)
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
    simpa [f] using normalizer_map_of_coprime_kernel hp_coprime hP_neBot hP_pgroup
  exact hasNormalPComplement_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hImage

/-- If `N ⊴ G` is a normal `p'`-subgroup, then a normal `p`-complement in
`C_G(P)` pushes to a normal `p`-complement in `C_{G/N}(Pbar)`.

This combines subgroup-image inheritance with Isaacs Lemma 7.7(b). -/
theorem hasNormalPComplement_centralizer_map_of_coprime_kernel
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_neBot : P ≠ ⊥) (hP_pgroup : IsPGroup p P)
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
    simpa [f] using centralizer_map_of_coprime_kernel hp_coprime hP_neBot hP_pgroup
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
  have hP_inf_N : P ⊓ N = ⊥ := Subgroup.inf_eq_bot_of_coprime h_coprime_PN
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
