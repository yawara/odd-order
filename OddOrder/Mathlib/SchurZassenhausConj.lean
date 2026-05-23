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

end SchurZassenhausConj

end Subgroup
