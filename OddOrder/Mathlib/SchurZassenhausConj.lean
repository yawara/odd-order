/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow

/-!
# Schur-Zassenhaus conjugacy (Isaacs Thm 3.12)

mathlib v4.29.1 provides existence (`Subgroup.exists_right_complement'_of_coprime`)
and abelian-case conjugacy (`Subgroup.exists_smul_eq` via `QuotientDiff`).
This file fills the **general-case conjugacy** assuming `N` or `G/N` is solvable
(Isaacs FGT Thm 3.12, mmd lines 1605-1665).

## Main result

* `Subgroup.IsComplement'.exists_conj_of_coprime`: For `N ⊴ G` finite with
  `(|N|, |G:N|) = 1` and `IsSolvable N ∨ IsSolvable (G ⧸ N)`, any two complements
  to `N` are conjugate by an element of `N`.

## Proof outline (Isaacs Thm 3.12)

Strong induction on `|G|`.

1. **Restriction** (`IsComplement'.subgroupOf_of_le`): if `K ≤ U ≤ G` and `K` complements
   `N`, then `K.subgroupOf U` complements `N.subgroupOf U` in `U`. Uses Dedekind modular
   law `(N ⊓ U) ⊔ K = U` (`K ≤ U`).
2. **Quotient** (`IsComplement'.map_mk'`): for `L ⊴ G`, complements push forward to
   complements in `G/L` (when `|K|` is coprime to `|N.map mk'|`).
3. **Main induction**: combine (1), (2), Sylow C-theorem, and abelian SZ conjugacy
   to handle the two solvability cases.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-! ### Helper B: Push a complement to a quotient -/

/-- If `K` complements `N ⊴ G` with coprime cardinalities, then the images of `N` and `K`
in `G/L` (any `L ⊴ G`) are also complements. (Isaacs Thm 3.12 proof, second paragraph.) -/
theorem IsComplement'.map_mk' {N K : Subgroup G} [Finite G] [N.Normal]
    (hK : IsComplement' N K) (h_cop : Nat.Coprime (Nat.card N) (Nat.card K))
    (L : Subgroup G) [L.Normal] :
    IsComplement' (N.map (QuotientGroup.mk' L)) (K.map (QuotientGroup.mk' L)) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · -- Disjoint via coprime cardinality.
    refine disjoint_iff.mpr (inf_eq_bot_of_coprime ?_)
    refine h_cop.coprime_dvd_left ?_ |>.coprime_dvd_right ?_
    · exact Subgroup.card_map_dvd _ _
    · exact Subgroup.card_map_dvd _ _
  · -- mul = univ via mk' surjective + N ⊔ K = ⊤.
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg_top : g ∈ (N ⊔ K : Subgroup G) := by rw [hK.sup_eq_top]; trivial
    rw [mem_sup_of_normal_left] at hg_top
    obtain ⟨n, hn, k, hk, hnk⟩ := hg_top
    refine ⟨QuotientGroup.mk n, ?_, QuotientGroup.mk k, ?_, ?_⟩
    · exact mem_map.mpr ⟨n, hn, rfl⟩
    · exact mem_map.mpr ⟨k, hk, rfl⟩
    · show (QuotientGroup.mk n : G ⧸ L) * QuotientGroup.mk k = QuotientGroup.mk g
      rw [← QuotientGroup.mk_mul, hnk]

/-! ### Helper A: Restriction of a complement to a containing subgroup -/

/-- If `K ≤ U ≤ G` and `K` complements `N ⊴ G`, then `K.subgroupOf U` complements
`N.subgroupOf U` in `U`. (Isaacs Thm 3.12 proof, first paragraph.) -/
theorem IsComplement'.subgroupOf_of_le {N K U : Subgroup G} [N.Normal]
    (hK : IsComplement' N K) (hKU : K ≤ U) :
    IsComplement' (N.subgroupOf U) (K.subgroupOf U) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · -- Disjoint (N.subgroupOf U) (K.subgroupOf U).
    rw [disjoint_iff]
    ext ⟨u, hu⟩
    simp only [mem_inf, mem_subgroupOf, mem_bot, Subtype.ext_iff, OneMemClass.coe_one]
    refine ⟨fun ⟨hN, hKmem⟩ => ?_, fun h => by simp [h]⟩
    have : u ∈ (N ⊓ K : Subgroup G) := ⟨hN, hKmem⟩
    rwa [hK.disjoint.eq_bot, mem_bot] at this
  · -- (N.subgroupOf U) * (K.subgroupOf U) = univ (in ↥U).
    rw [Set.eq_univ_iff_forall]
    rintro ⟨u, hu⟩
    -- Decompose u = n * k via N ⊔ K = ⊤ (N normal: use mem_sup_of_normal_left).
    have hu_top : (u : G) ∈ (N ⊔ K : Subgroup G) := by rw [hK.sup_eq_top]; trivial
    rw [mem_sup_of_normal_left] at hu_top
    obtain ⟨n, hn, k, hk, hnk⟩ := hu_top
    have hkU : k ∈ U := hKU hk
    have hnU : n ∈ U := by
      have heq : n = u * k⁻¹ := by rw [← hnk]; group
      rw [heq]
      exact U.mul_mem hu (U.inv_mem hkU)
    refine ⟨⟨n, hnU⟩, mem_subgroupOf.mpr hn, ⟨k, hkU⟩, mem_subgroupOf.mpr hk, ?_⟩
    ext; simpa using hnk

/-! ### Main induction (Isaacs Thm 3.12) -/

universe u

namespace SchurZassenhausConj

/-- Induction hypothesis form: SZ conjugacy for groups of strictly smaller cardinality. -/
private def IH (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (G' : Type u) [Group G'] [Finite G'],
    Nat.card G' < Nat.card G → ∀ {N' : Subgroup G'} [N'.Normal],
      Nat.Coprime (Nat.card N') N'.index →
      (IsSolvable N' ∨ IsSolvable (G' ⧸ N')) →
      ∀ {K K' : Subgroup G'}, IsComplement' N' K → IsComplement' N' K' →
      ∃ n : G', n ∈ N' ∧ K.map (MulAut.conj n).toMonoidHom = K'

variable {G : Type u} [Group G]

/-- Subgroup ⊆ inclusion of subgroupOf to N: `↥(N.subgroupOf U) →* ↥N`. -/
private def subgroupOfInclToN (N U : Subgroup G) : ↥(N.subgroupOf U) →* ↥N where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem subgroupOfInclToN_injective (N U : Subgroup G) :
    Function.Injective (subgroupOfInclToN N U) := by
  intro x y h
  simp only [subgroupOfInclToN, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.mk.injEq] at h
  exact Subtype.ext (Subtype.ext h)

/-- `IsSolvable N ⇒ IsSolvable (N.subgroupOf U)`. -/
instance subgroupOf_isSolvable_of_isSolvable (N U : Subgroup G) [IsSolvable N] :
    IsSolvable (N.subgroupOf U) :=
  solvable_of_solvable_injective (subgroupOfInclToN_injective N U)

/-- `IsSolvable (G ⧸ N) ⇒ IsSolvable (U ⧸ N.subgroupOf U)` for any `U ≤ G`.
Proof: `U ⧸ N.subgroupOf U ≃ (U ⊔ N) ⧸ N.subgroupOf (U ⊔ N)` (second iso theorem), and
the latter embeds into `G ⧸ N` via `QuotientGroup.lift`. -/
instance quotient_subgroupOf_isSolvable_of_quotient {U N : Subgroup G} [N.Normal]
    [IsSolvable (G ⧸ N)] : IsSolvable (U ⧸ N.subgroupOf U) := by
  -- Step 1: define φ : (U ⊔ N) ⧸ N.subgroupOf (U ⊔ N) →* G ⧸ N via lift.
  let φ : ((U ⊔ N : Subgroup G) ⧸ N.subgroupOf (U ⊔ N)) →* G ⧸ N :=
    QuotientGroup.lift (N.subgroupOf (U ⊔ N))
      ((QuotientGroup.mk' N).comp (U ⊔ N).subtype)
      (fun x hx => by
        show (QuotientGroup.mk x.val : G ⧸ N) = 1
        exact (QuotientGroup.eq_one_iff _).mpr hx)
  have hφ_inj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x⟩ hx
    rw [MonoidHom.mem_ker] at hx
    change (QuotientGroup.mk x.val : G ⧸ N) = 1 at hx
    rw [QuotientGroup.eq_one_iff] at hx
    -- ⟦x⟧ = 1 in (U ⊔ N) ⧸ N.subgroupOf (U ⊔ N): x ∈ N.subgroupOf (U ⊔ N).
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).mpr hx
  haveI hUN : IsSolvable ((U ⊔ N : Subgroup G) ⧸ N.subgroupOf (U ⊔ N)) :=
    solvable_of_solvable_injective hφ_inj
  -- Step 2: Transfer back via second iso (direction U ⧸ ... → (U ⊔ N) ⧸ ...).
  let e := QuotientGroup.quotientInfEquivProdNormalQuotient U N
  exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective

/-! ### Helper lemmas for IH termination -/

variable [Finite G]

/-- `L ≠ ⊥ ⇒ |G ⧸ L| < |G|` for finite `G`. -/
private theorem card_quotient_lt_of_ne_bot {L : Subgroup G} [L.Normal] (hL : L ≠ ⊥) :
    Nat.card (G ⧸ L) < Nat.card G := by
  show L.index < Nat.card G
  have h_L_gt : 1 < Nat.card ↥L := (Subgroup.one_lt_card_iff_ne_bot _).mpr hL
  have h_L_idx_pos : 0 < L.index := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    have : Nat.card G = 0 := by rw [← L.card_mul_index, h]; ring
    exact absurd this Nat.card_pos.ne'
  calc L.index = L.index * 1 := (mul_one _).symm
    _ < L.index * Nat.card ↥L := (Nat.mul_lt_mul_left h_L_idx_pos).mpr h_L_gt
    _ = Nat.card G := L.index_mul_card

variable {N : Subgroup G} [N.Normal]

/-! ### Step 1: Restriction reduction (proper subgroup `U`) -/

/-- `(K.subgroupOf U).map U.subtype = K` when `K ≤ U`. -/
private theorem subgroupOf_map_subtype_eq {U K : Subgroup G} (hKU : K ≤ U) :
    (K.subgroupOf U).map U.subtype = K := by
  rw [subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hKU]

/-- Conjugation by `n' : ↥U` in `↥U` corresponds (via `U.subtype`) to conjugation by `n'.val` in `G`. -/
private theorem subtype_comp_conj_eq {U : Subgroup G} (n' : ↥U) :
    U.subtype.comp ((MulAut.conj n').toMonoidHom) =
      ((MulAut.conj (n'.val : G)).toMonoidHom).comp U.subtype := by
  ext ⟨x, hx⟩
  rfl

/-- Pushing `((K.subgroupOf U).map (conj n')).map U.subtype` equals `K.map (conj n'.val)`. -/
private theorem map_subtype_conj_subgroupOf {U : Subgroup G} (n' : ↥U) (K : Subgroup G)
    (hKU : K ≤ U) :
    ((K.subgroupOf U).map (MulAut.conj n').toMonoidHom).map U.subtype =
      K.map (MulAut.conj (n'.val : G)).toMonoidHom := by
  rw [Subgroup.map_map, subtype_comp_conj_eq, ← Subgroup.map_map, subgroupOf_map_subtype_eq hKU]

/-- **Step 1 (Restriction)**: if `K, K' ≤ U < ⊤`, the inductive hypothesis applied to `↥U`
gives an element `n ∈ N` conjugating `K` to `K'`. -/
private theorem step_restriction
    (h1 : Nat.Coprime (Nat.card N) N.index)
    (hSolv : IsSolvable N ∨ IsSolvable (G ⧸ N))
    (ih : IH G)
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K')
    {U : Subgroup G} (hKU : K ≤ U) (hK'U : K' ≤ U) (hU_lt : U ≠ ⊤) :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' := by
  -- |↥U| < |G| via Lagrange + index > 1.
  have hcard_lt : Nat.card ↥U < Nat.card G := by
    have h_idx : 1 < U.index := Subgroup.one_lt_index_of_ne_top hU_lt
    calc Nat.card ↥U = Nat.card ↥U * 1 := (mul_one _).symm
      _ < Nat.card ↥U * U.index := (Nat.mul_lt_mul_left Nat.card_pos).mpr h_idx
      _ = Nat.card G := Subgroup.card_mul_index U
  -- Coprime |N.subgroupOf U| (N.subgroupOf U).index.
  have h_card_dvd : Nat.card (N.subgroupOf U) ∣ Nat.card N :=
    Subgroup.card_comap_dvd_of_injective N U.subtype U.subtype_injective
  have h_index_dvd : (N.subgroupOf U).index ∣ N.index :=
    Subgroup.relIndex_dvd_index_of_normal N U
  have h_cop : Nat.Coprime (Nat.card (N.subgroupOf U)) (N.subgroupOf U).index :=
    (h1.coprime_dvd_left h_card_dvd).coprime_dvd_right h_index_dvd
  -- Solvability transfer.
  have h_solv : IsSolvable (N.subgroupOf U) ∨ IsSolvable (↥U ⧸ N.subgroupOf U) := by
    rcases hSolv with h | h
    · left; haveI := h; infer_instance
    · right; haveI := h; infer_instance
  -- Helper A: restrict complements to ↥U.
  have hK_U : IsComplement' (N.subgroupOf U) (K.subgroupOf U) := hK.subgroupOf_of_le hKU
  have hK'_U : IsComplement' (N.subgroupOf U) (K'.subgroupOf U) := hK'.subgroupOf_of_le hK'U
  -- Apply IH.
  obtain ⟨n', hn'_mem, hconj⟩ := ih ↥U hcard_lt h_cop h_solv hK_U hK'_U
  -- Lift n' to n'.val ∈ G (which is ∈ N via mem_subgroupOf).
  refine ⟨n'.val, hn'_mem, ?_⟩
  -- Push hconj via U.subtype.
  have hpush : ((K.subgroupOf U).map (MulAut.conj n').toMonoidHom).map U.subtype =
               (K'.subgroupOf U).map U.subtype := by rw [hconj]
  rw [map_subtype_conj_subgroupOf n' K hKU, subgroupOf_map_subtype_eq hK'U] at hpush
  exact hpush

/-! ### Step 2 (Factor) / Case A (N solvable) / Case B (G/N solvable)

These are still in progress. The skeleton below defines the statements and the main_aux
assembly; the bodies (marked `sorry`) need to be filled. -/

/-- Conjugation `mk'_comp_conj`: in `G ⧸ L`, conjugation by `mk' g` agrees with `mk'` applied
to conjugation by `g`. Used in the lift-back step of `step_factor`. -/
private theorem mk'_comp_conj_eq {L : Subgroup G} [L.Normal] (g : G) :
    (QuotientGroup.mk' L).comp (MulAut.conj g).toMonoidHom =
      ((MulAut.conj (QuotientGroup.mk g : G ⧸ L)).toMonoidHom).comp (QuotientGroup.mk' L) := by
  ext x
  show (QuotientGroup.mk (g * x * g⁻¹) : G ⧸ L) =
       (QuotientGroup.mk g) * (QuotientGroup.mk x) * (QuotientGroup.mk g)⁻¹
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

/-- **Step 2 (Factor)**: for nontrivial `L ⊴ G`, IH on `G ⧸ L` gives `g ∈ N` with
`(K^g) ⊔ L = K' ⊔ L`. -/
private theorem step_factor
    (h1 : Nat.Coprime (Nat.card N) N.index)
    (hSolv : IsSolvable N ∨ IsSolvable (G ⧸ N))
    (ih : IH G)
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K')
    {L : Subgroup G} [L.Normal] (hL_ne_bot : L ≠ ⊥) :
    ∃ g : G, g ∈ N ∧ (K.map (MulAut.conj g).toMonoidHom) ⊔ L = K' ⊔ L := by
  -- |G/L| < |G|.
  have hcard_lt := card_quotient_lt_of_ne_bot hL_ne_bot
  -- Coprime cardinalities for Helper B.
  have h_NK_cop : Nat.Coprime (Nat.card N) (Nat.card K) := by
    rw [show Nat.card K = N.index from hK.symm.index_eq_card.symm]
    exact h1
  have h_NK'_cop : Nat.Coprime (Nat.card N) (Nat.card K') := by
    rw [show Nat.card K' = N.index from hK'.symm.index_eq_card.symm]
    exact h1
  -- Helper B: complements in G/L.
  have hK_q : IsComplement' (N.map (QuotientGroup.mk' L)) (K.map (QuotientGroup.mk' L)) :=
    hK.map_mk' h_NK_cop L
  have hK'_q : IsComplement' (N.map (QuotientGroup.mk' L)) (K'.map (QuotientGroup.mk' L)) :=
    hK'.map_mk' h_NK'_cop L
  -- Coprime in G/L.
  have h_cop_q : Nat.Coprime (Nat.card (N.map (QuotientGroup.mk' L)))
                  (N.map (QuotientGroup.mk' L)).index :=
    (h1.coprime_dvd_left (Subgroup.card_map_dvd _ _)).coprime_dvd_right
      (N.index_map_dvd (QuotientGroup.mk'_surjective L))
  -- Solvability transfer to G/L.
  have h_solv_q : IsSolvable (N.map (QuotientGroup.mk' L)) ∨
                   IsSolvable ((G ⧸ L) ⧸ (N.map (QuotientGroup.mk' L))) := by
    rcases hSolv with h | h
    · left
      haveI : IsSolvable N := h
      -- N → N.map mk' is surjective.
      let f : N →* ↥(N.map (QuotientGroup.mk' L)) :=
        ((QuotientGroup.mk' L).comp N.subtype).codRestrict _ (fun x =>
          Subgroup.mem_map.mpr ⟨x.val, x.property, rfl⟩)
      have hf_surj : Function.Surjective f := by
        rintro ⟨y, hy⟩
        obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨n, hn⟩, by ext; exact hny⟩
      exact solvable_of_surjective hf_surj
    · right
      haveI : IsSolvable (G ⧸ N) := h
      -- (G ⧸ L) ⧸ (N.map mk') is quotient of (G ⧸ N) via lift.
      -- φ : G ⧸ N →* (G ⧸ L) ⧸ (N.map mk') sending ⟦g⟧_N ↦ ⟦⟦g⟧_L⟧_{N.map mk'}.
      let φ : G ⧸ N →* (G ⧸ L) ⧸ (N.map (QuotientGroup.mk' L)) :=
        QuotientGroup.lift N
          ((QuotientGroup.mk' (N.map (QuotientGroup.mk' L))).comp (QuotientGroup.mk' L))
          (fun n hn => by
            show (QuotientGroup.mk (QuotientGroup.mk n : G ⧸ L) :
                  (G ⧸ L) ⧸ (N.map (QuotientGroup.mk' L))) = 1
            rw [QuotientGroup.eq_one_iff]
            exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
      have hφ_surj : Function.Surjective φ := by
        rintro ⟨⟨g⟩⟩
        exact ⟨QuotientGroup.mk g, rfl⟩
      exact solvable_of_surjective hφ_surj
  -- Apply IH on G/L.
  obtain ⟨x, hx_mem, hx_conj⟩ := ih (G ⧸ L) hcard_lt h_cop_q h_solv_q hK_q hK'_q
  -- Lift x to g ∈ N.
  obtain ⟨g, hg_N, hg_eq⟩ := Subgroup.mem_map.mp hx_mem
  refine ⟨g, hg_N, ?_⟩
  -- Translate (K.map (conj g)).map mk' = K'.map mk' to G level via map_eq_map_iff.
  have key : (K.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' L) =
             K'.map (QuotientGroup.mk' L) := by
    rw [Subgroup.map_map, mk'_comp_conj_eq, ← Subgroup.map_map]
    rw [show (QuotientGroup.mk g : G ⧸ L) = x from hg_eq]
    exact hx_conj
  have heq := (Subgroup.map_eq_map_iff (f := QuotientGroup.mk' L)).mp key
  rwa [QuotientGroup.ker_mk'] at heq

/-- Isaacs Lem 3.11: minimal `G`-normal of solvable group is commutative.
mathlib v4.29.1 にこの形の lemma がないため自前. -/
private theorem minimal_normal_isCommutative_of_solvable
    {N L : Subgroup G} [N.Normal] [L.Normal] (hL_le : L ≤ N) (hL_ne : L ≠ ⊥)
    (hL_min : ∀ L' : Subgroup G, L'.Normal → L' ≤ L → L' ≠ ⊥ → L' = L)
    (hN_solv : IsSolvable N) : IsMulCommutative L := by
  haveI hN_solv' : IsSolvable N := hN_solv
  -- [L, L] ≤ L, [L, L] is G-normal.
  have h_LL_le : ⁅L, L⁆ ≤ L := Subgroup.commutator_le_self L
  haveI h_LL_normal : (⁅L, L⁆ : Subgroup G).Normal := Subgroup.commutator_normal L L
  -- By minimality, [L, L] = ⊥ or [L, L] = L.
  by_cases h : (⁅L, L⁆ : Subgroup G) = ⊥
  · -- [L, L] = ⊥ ⇒ L is commutative in G ⇒ IsMulCommutative L.
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha_cent : (a : G) ∈ Subgroup.centralizer L := h a.property
    rw [Subgroup.mem_centralizer_iff] at ha_cent
    apply Subtype.ext
    exact (ha_cent b.val b.property).symm
  · -- [L, L] = L, contradiction with solvability of L (subgroup of solvable N).
    exfalso
    have h_eq : (⁅L, L⁆ : Subgroup G) = L := hL_min _ h_LL_normal h_LL_le h
    -- L ≃* L.subgroupOf N, the latter is solvable, hence L solvable.
    haveI hL_solv : IsSolvable L := by
      haveI : IsSolvable (L.subgroupOf N) := inferInstance
      let e := (subgroupOfEquivOfLe hL_le).symm
      exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
    -- ⁅⊤_L, ⊤_L⁆.map L.subtype = ⁅L, L⁆.
    have h_comm_map : (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L).map L.subtype = ⁅L, L⁆ := by
      rw [Subgroup.map_commutator, ← L.subtype.range_eq_map, Subgroup.range_subtype]
    -- ⁅L, L⁆ = L = L.subtype.range.
    have h_map_range : (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L).map L.subtype = L.subtype.range := by
      rw [h_comm_map, h_eq, Subgroup.range_subtype]
    -- ⁅⊤_L, ⊤_L⁆ = ⊤ in ↥L (via map_eq_range_iff).
    have h_comm_top : (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L) = ⊤ := by
      have := Subgroup.map_eq_range_iff.mp h_map_range
      rw [show L.subtype.ker = ⊥ from L.ker_subtype] at this
      exact codisjoint_bot.mp this
    -- By induction, derivedSeries L n = ⊤ for all n.
    have h_ds_top : ∀ n, derivedSeries L n = ⊤ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [derivedSeries_succ]; rw [ih]; exact h_comm_top
    -- L is nontrivial (since L ≠ ⊥ in G).
    haveI : Nontrivial ↥L := (Subgroup.bot_or_nontrivial L).resolve_left hL_ne
    -- L solvable: derivedSeries L n = ⊥ for some n.
    obtain ⟨n, hn⟩ := hL_solv.solvable
    -- Contradiction: (⊤ : Subgroup ↥L) = ⊥.
    rw [h_ds_top] at hn
    exact bot_lt_top.ne' hn

/-- **Abelian SZ conjugacy**: for `N` abelian normal in `G` with coprime order/index,
any two complements are conjugate by an element of `N`. mathlib's `exists_smul_eq`
provides the abstract `QuotientDiff` form; we translate to the subgroup-level statement.

TODO (sorry remaining at the end): the final piece requires converting the equivalence
`n • [TK] = [TK']` in `N.QuotientDiff` into the subgroup equation `K^n = K'`. This is
non-trivial: `diff = 1` equivalence relates transversals only setwise (each coset rep
differs by an N element with product 1), not as subgroups. May need a Lean tactic chain
through `Quotient.exact'` + `smul_diff_smul'` + cardinality. -/
private theorem abelian_sz_conjugacy
    {N : Subgroup G} [N.Normal] [Finite G] [IsMulCommutative N]
    (hN : Nat.Coprime (Nat.card N) N.index)
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K') :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' := by
  -- Construct LeftTransversals from complements.
  let TK : N.LeftTransversal := ⟨(K : Set G), hK.symm⟩
  let TK' : N.LeftTransversal := ⟨(K' : Set G), hK'.symm⟩
  -- Form QuotientDiff classes.
  let αK : N.QuotientDiff := Quotient.mk'' TK
  let αK' : N.QuotientDiff := Quotient.mk'' TK'
  -- Apply mathlib exists_smul_eq (requires [FiniteIndex N], auto from [Finite G] instance).
  obtain ⟨⟨n, hn⟩, hsmul⟩ := Subgroup.exists_smul_eq hN αK αK'
  refine ⟨n, hn, ?_⟩
  -- hsmul : (⟨n, hn⟩ : ↥N) • αK = αK' (in N.QuotientDiff).
  -- Need: K.map (conj n) = K' (subgroup conjugation).
  -- TODO: technical transition via Quotient.exact' + diff = 1 + subgroup characterization.
  sorry

/-- Existence of a minimal `G`-normal subgroup contained in nontrivial `N`. -/
private theorem exists_minimal_normal_le {N : Subgroup G} (hN_normal : N.Normal) (hN : N ≠ ⊥) :
    ∃ L : Subgroup G, L.Normal ∧ L ≤ N ∧ L ≠ ⊥ ∧
      ∀ L' : Subgroup G, L'.Normal → L' ≤ L → L' ≠ ⊥ → L' = L := by
  let S : Set (Subgroup G) := {L | L.Normal ∧ L ≤ N ∧ L ≠ ⊥}
  have hS_fin : S.Finite := Set.toFinite S
  have hS_ne : S.Nonempty := ⟨N, hN_normal, le_refl N, hN⟩
  obtain ⟨L, hL_min⟩ := hS_fin.exists_minimal hS_ne
  -- hL_min : Minimal (· ∈ S) L
  obtain ⟨⟨hL_normal, hL_le, hL_ne⟩, hL_minimal⟩ := hL_min
  refine ⟨L, hL_normal, hL_le, hL_ne, ?_⟩
  intro L' hL'_normal hL'_le hL'_ne
  have hL'_mem : L' ∈ S := ⟨hL'_normal, hL'_le.trans hL_le, hL'_ne⟩
  -- hL_minimal : ∀ b ∈ S, b ≤ L → L ≤ b
  exact le_antisymm hL'_le (hL_minimal hL'_mem hL'_le)

/-- **Case A (N solvable)**: full SZ conjugacy when `N` is solvable.

Strategy: take minimal normal `L ⊆ N` in `G`, which is abelian (Isaacs Lem 3.11). Apply
step_factor with `L` to get `g ∈ N` with `K^g · L = K' · L =: HL`. If `HL < G`, apply
step_restriction. If `HL = G`, then `L = N` (cardinality), so `N` is abelian and we use
mathlib `Subgroup.exists_smul_eq` (abelian SZ conjugacy). -/
private theorem step_caseA
    (h1 : Nat.Coprime (Nat.card N) N.index)
    (hN_solv : IsSolvable N)
    (ih : IH G)
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K') :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' := by
  -- Trivial case: N = ⊥ ⇒ K = K' = ⊤.
  by_cases hN_bot : N = ⊥
  · subst hN_bot
    have hK_top : K = ⊤ := by
      have := hK.sup_eq_top
      rwa [bot_sup_eq] at this
    have hK'_top : K' = ⊤ := by
      have := hK'.sup_eq_top
      rwa [bot_sup_eq] at this
    refine ⟨1, (⊥ : Subgroup G).one_mem, ?_⟩
    rw [hK_top, hK'_top]
    ext x
    simp [Subgroup.mem_map]
  -- Nontrivial case: take minimal normal L ⊆ N, abelian, then case split on K^g ⊔ L.
  haveI hN_normal_inst : N.Normal := inferInstance
  obtain ⟨L, hL_normal, hL_le, hL_ne_bot, hL_min⟩ :=
    exists_minimal_normal_le hN_normal_inst hN_bot
  haveI : L.Normal := hL_normal
  haveI hL_comm : IsMulCommutative L :=
    minimal_normal_isCommutative_of_solvable hL_le hL_ne_bot hL_min hN_solv
  -- Apply step_factor with L.
  obtain ⟨g_f, hg_f_N, h_factor⟩ :=
    step_factor h1 (Or.inl hN_solv) ih hK hK' hL_ne_bot
  -- h_factor : (K.map (conj g_f)) ⊔ L = K' ⊔ L
  -- Need: IsComplement' N K^g (K conjugated by g_f ∈ N, N normal preserves complement).
  have hK_g_compl : IsComplement' N (K.map (MulAut.conj g_f).toMonoidHom) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ
    · -- Disjoint: N ⊓ K^g_f = ⊥.
      rw [disjoint_iff]
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_bot, Subgroup.mem_map,
                 MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine ⟨fun ⟨hxN, k, hkK, hkx⟩ => ?_, fun h => ?_⟩
      · -- k = g_f⁻¹ * x * g_f. Both x ∈ N and g_f ∈ N ⇒ k ∈ N. K ⊓ N = ⊥ ⇒ k = 1 ⇒ x = 1.
        have hk_eq : k = g_f⁻¹ * x * g_f := by rw [← hkx]; group
        have hkN : k ∈ N := by
          rw [hk_eq]
          exact N.mul_mem (N.mul_mem (N.inv_mem hg_f_N) hxN) hg_f_N
        have hk_inter : k ∈ N ⊓ K := ⟨hkN, hkK⟩
        rw [hK.disjoint.eq_bot, Subgroup.mem_bot] at hk_inter
        rw [hk_inter, mul_one, mul_inv_cancel] at hkx
        exact hkx.symm
      · subst h
        exact ⟨N.one_mem, 1, K.one_mem, by simp⟩
    · -- (N : Set G) * (K^g_f : Set G) = univ.
      rw [Set.eq_univ_iff_forall]
      intro x
      -- Decompose g_f⁻¹ x g_f = n' * k' in N + K, then conjugate back.
      have h_conj_in_sup : g_f⁻¹ * x * g_f ∈ (N ⊔ K : Subgroup G) := by
        rw [hK.sup_eq_top]; trivial
      rw [mem_sup_of_normal_left] at h_conj_in_sup
      obtain ⟨n', hn'_N, k', hk'_K, hnk'⟩ := h_conj_in_sup
      have hN_normal_inst' : N.Normal := inferInstance
      refine ⟨g_f * n' * g_f⁻¹, hN_normal_inst'.conj_mem n' hn'_N g_f,
              g_f * k' * g_f⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨k', hk'_K, rfl⟩
      · -- (g_f n' g_f⁻¹) * (g_f k' g_f⁻¹) = g_f (n' k') g_f⁻¹ = g_f (g_f⁻¹ x g_f) g_f⁻¹ = x.
        show g_f * n' * g_f⁻¹ * (g_f * k' * g_f⁻¹) = x
        have : g_f * n' * g_f⁻¹ * (g_f * k' * g_f⁻¹) = g_f * (n' * k') * g_f⁻¹ := by group
        rw [this, hnk']
        group
  -- Case split on K^g ⊔ L = ⊤.
  by_cases hH_top : (K.map (MulAut.conj g_f).toMonoidHom) ⊔ L = ⊤
  · -- N = L (cardinality), N abelian, abelian SZ conjugacy.
    -- K^g_f ⊓ L ⊆ K^g_f ⊓ N = ⊥.
    have h_inter_bot : (K.map (MulAut.conj g_f).toMonoidHom) ⊓ L = ⊥ := by
      apply le_bot_iff.mp
      have h_KgN : (K.map (MulAut.conj g_f).toMonoidHom) ⊓ N = ⊥ := by
        rw [inf_comm]; exact hK_g_compl.disjoint.eq_bot
      calc (K.map (MulAut.conj g_f).toMonoidHom) ⊓ L
          ≤ (K.map (MulAut.conj g_f).toMonoidHom) ⊓ N := inf_le_inf_left _ hL_le
        _ = ⊥ := h_KgN
    -- |K^g_f| * |L| = |G| (from disjoint + sup_eq_top via IsComplement').
    have hKgL_compl : IsComplement' (K.map (MulAut.conj g_f).toMonoidHom) L := by
      apply isComplement'_of_disjoint_and_mul_eq_univ
      · rw [disjoint_iff]; exact h_inter_bot
      · -- Set product = univ via mem_sup_of_normal_right (L normal).
        rw [Set.eq_univ_iff_forall]
        intro x
        have hx_top : x ∈ (K.map (MulAut.conj g_f).toMonoidHom ⊔ L : Subgroup G) := by
          rw [hH_top]; trivial
        rw [mem_sup_of_normal_right] at hx_top
        obtain ⟨k, hk, l, hl, hkl⟩ := hx_top
        exact ⟨k, hk, l, hl, hkl⟩
    -- |L| = |N| from |K^g_f| * |L| = |G| = |N| * |K^g_f|.
    have h_card_L_eq_N : Nat.card ↥L = Nat.card N := by
      have h1' : Nat.card (K.map (MulAut.conj g_f).toMonoidHom) * Nat.card ↥L = Nat.card G :=
        hKgL_compl.card_mul
      have h2' : Nat.card ↥N * Nat.card (K.map (MulAut.conj g_f).toMonoidHom) = Nat.card G :=
        hK_g_compl.card_mul
      have h_swap : Nat.card (K.map (MulAut.conj g_f).toMonoidHom) * Nat.card ↥N = Nat.card G := by
        rw [mul_comm]; exact h2'
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1'.trans h_swap.symm)
    -- L = N (from L ≤ N + |L| = |N|).
    have hL_eq_N : L = N :=
      Subgroup.eq_of_le_of_card_ge hL_le h_card_L_eq_N.ge
    -- Now N = L abelian. Use abelian SZ conjugacy.
    subst hL_eq_N
    -- hL_comm : IsMulCommutative L = IsMulCommutative N. Original hK, hK' still in scope.
    exact abelian_sz_conjugacy h1 hK hK'
  · -- H = K^g ⊔ L is proper, apply step_restriction.
    have hKgU : K.map (MulAut.conj g_f).toMonoidHom ≤
                K.map (MulAut.conj g_f).toMonoidHom ⊔ L := le_sup_left
    have hK'U : K' ≤ K.map (MulAut.conj g_f).toMonoidHom ⊔ L := by
      rw [h_factor]; exact le_sup_left
    obtain ⟨n', hn'_N, h_conj⟩ :=
      step_restriction h1 (Or.inl hN_solv) ih hK_g_compl hK' hKgU hK'U hH_top
    -- Compose conjugations: K.map (conj (n' * g_f)) = (K.map (conj g_f)).map (conj n') = K'
    refine ⟨n' * g_f, N.mul_mem hn'_N hg_f_N, ?_⟩
    rw [show (MulAut.conj (n' * g_f)).toMonoidHom =
          (MulAut.conj n').toMonoidHom.comp (MulAut.conj g_f).toMonoidHom from ?_,
        ← Subgroup.map_map]
    · exact h_conj
    · ext x
      show n' * g_f * x * (n' * g_f)⁻¹ = n' * (g_f * x * g_f⁻¹) * n'⁻¹
      group

/-- **Case B (G/N solvable)**: full SZ conjugacy when `G ⧸ N` is solvable. -/
private theorem step_caseB
    (h1 : Nat.Coprime (Nat.card N) N.index)
    (hQN_solv : IsSolvable (G ⧸ N))
    (ih : IH G)
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K') :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' := by
  -- Trivial case: N = ⊤ ⇒ K = K' = ⊥.
  by_cases hN_top : N = ⊤
  · subst hN_top
    have hK_bot : K = ⊥ := by
      have h_inf : ⊤ ⊓ K = ⊥ := hK.disjoint.eq_bot
      rwa [top_inf_eq] at h_inf
    have hK'_bot : K' = ⊥ := by
      have h_inf : ⊤ ⊓ K' = ⊥ := hK'.disjoint.eq_bot
      rwa [top_inf_eq] at h_inf
    refine ⟨1, (⊤ : Subgroup G).one_mem, ?_⟩
    rw [hK_bot, hK'_bot]
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_bot]
  -- Main: minimal normal M/N + Sylow C + N_G(L) argument.
  -- N ≠ ⊤. G/N nontrivial + solvable.
  -- Take minimal normal M̄ ⊆ G/N (use exists_minimal_normal_le on G/N).
  -- M := M̄.comap (mk' N). N ≤ M ≤ G.
  -- M̄ is p-group (minimal normal of solvable ⇒ elementary abelian p-group via Lem 3.11 extension).
  -- M ∩ K, M ∩ K^g are Sylow p in M (since coprime, |M ∩ K| = |M:N| = |M̄|).
  -- Sylow C in M: ∃ m ∈ M, (M ∩ K)^m = M ∩ K^g.
  -- L := M ∩ K normal in K, K^(g*m).
  -- ⟨K, K^(g*m)⟩ ≤ N_G(L). Case N_G(L) < G: apply step_restriction.
  -- Case N_G(L) = G: L ⊴ G. step_factor with L gives K^h ⊔ L = K' ⊔ L.
  -- ... lengthy case analysis.
  sorry

/-- **Main induction**: combines `step_caseA` and `step_caseB` via strong induction. -/
private theorem main_aux {n : ℕ} :
    ∀ {G : Type u} [Group G] [Finite G] (_hG : Nat.card G = n)
      {N : Subgroup G} [N.Normal]
      (h1 : Nat.Coprime (Nat.card N) N.index)
      (hSolv : IsSolvable N ∨ IsSolvable (G ⧸ N))
      {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K'),
      ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G _ _ hG N _ h1 hSolv K K' hK hK'
    -- Build IH G from outer ih.
    have ih_G : IH G := by
      intro G' _ _ hcard_G' N' _ h1' hSolv' K1 K2 hK1 hK2
      exact ih (Nat.card G') (hG ▸ hcard_G') rfl h1' hSolv' hK1 hK2
    rcases hSolv with hN | hGN
    · exact step_caseA h1 hN ih_G hK hK'
    · exact step_caseB h1 hGN ih_G hK hK'

end SchurZassenhausConj

/-- **Schur-Zassenhaus conjugacy** (Isaacs Thm 3.12): for `N ⊴ G` finite with coprime order
and index, assuming `N` or `G ⧸ N` is solvable, any two complements are conjugate by an
element of `N`. -/
theorem IsComplement'.exists_conj_of_coprime {G : Type u} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index)
    (hSolv : IsSolvable N ∨ IsSolvable (G ⧸ N))
    {K K' : Subgroup G} (hK : IsComplement' N K) (hK' : IsComplement' N K') :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K' :=
  SchurZassenhausConj.main_aux rfl hN hSolv hK hK'

end Subgroup
