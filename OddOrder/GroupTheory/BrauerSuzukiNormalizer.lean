import Mathlib.GroupTheory.Transfer
import OddOrder.GroupTheory.BrauerSuzukiSetup
import OddOrder.GroupTheory.SylowNormalRelIndex

/-!
# Brauer–Suzuki: the structure of `N = N_G(T)` (Gorenstein Ch. 12, Lemma 1.2)

**Gorenstein, *Finite Groups*, Ch. 12, Lemma 1.2** (p. 374): in the
`QuaternionSylowSetup` (issue 9318), with `T = ⟨x²⟩`, `C = C_G(T)`, `N = N_G(T)`:

(i) `N = SH` where `H ⊴ N` and `|H|` is odd; (ii) `C = XH`.

This file develops the proof along the book's lines:

* `C_le_N` / the `Normal` instance for `C.subgroupOf N` — `C ⊴ N`;
* `two_not_dvd_relIndex_C` — `X = S ∩ C` is a Sylow `2`-subgroup of `C` in index form
  (`2 ∤ [C : X]`), via `sylow_relIndex_normal_not_dvd` inside `N`;
* `exists_sylow_C_eq` — a bundled cyclic Sylow `2`-subgroup of `C` with carrier
  `X.subgroupOf C`.

The Burnside normal `2`-complement `H` of `C` and the assembly `N = SH`, `C = XH`
follow in the sequel.
-/

namespace OddOrder.GroupTheory

namespace QuaternionSylowSetup

open Subgroup

variable {G : Type*} [Group G] [Finite G] (Q : QuaternionSylowSetup G)

/-- `C = C_G(T) ≤ N_G(T) = N`. -/
theorem C_le_N : Q.C ≤ Q.N :=
  centralizer_le_normalizer (Q.T : Set G)

/-- **`C ⊴ N`** (Gorenstein p. 374): the centralizer is normal in the normalizer. -/
instance : (Q.C.subgroupOf Q.N).Normal :=
  normal_subgroupOf_centralizer_normalizer (Q.T : Set G)

/-- `X` is a `2`-group of order `2ⁿ`. -/
theorem card_X : Nat.card Q.X = 2 ^ Q.n := by
  rw [X, Nat.card_zpowers, Q.hx_order]

/-- **`X` is a Sylow `2`-subgroup of `C`, index form** (Gorenstein p. 374): the
relative index `[C : X]` is odd.  Obtained from `S ∩ C = X` and the
Sylow-intersect-normal lemma applied inside `N` (where `C` is normal). -/
theorem two_not_dvd_relIndex_C : ¬ 2 ∣ Q.X.relIndex Q.C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the Sylow-intersect-normal lemma inside `↥N`
  have h := sylow_relIndex_normal_not_dvd (Q.S.subtype Q.S_le_N) (Q.C.subgroupOf Q.N)
  rw [Sylow.coe_subtype, relIndex_subgroupOf Q.C_le_N] at h
  -- `[C : S] = [C : S ⊓ C] = [C : X]`
  rwa [← inf_relIndex_right, Q.S_inf_C_eq_X] at h

/-- `x ∈ C`. -/
theorem x_mem_C : Q.x ∈ Q.C :=
  Q.X_le_C (Q.mem_X_iff.mpr ⟨1, (zpow_one Q.x).symm⟩)

/-- **A cyclic Sylow `2`-subgroup of `C` with carrier `X`** (Gorenstein p. 374):
there is a Sylow `2`-subgroup of `C` equal to `X.subgroupOf C`; it is cyclic. -/
theorem exists_sylow_C_eq :
    ∃ P : Sylow 2 ↥Q.C, (P : Subgroup ↥Q.C) = Q.X.subgroupOf Q.C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `X.subgroupOf C` is a `2`-group…
  have hcard : Nat.card (Q.X.subgroupOf Q.C) = 2 ^ Q.n := by
    rw [Nat.card_congr (subgroupOfEquivOfLe Q.X_le_C).toEquiv, Q.card_X]
  have hp : IsPGroup 2 (Q.X.subgroupOf Q.C) := IsPGroup.of_card hcard
  -- …contained in some Sylow `2`-subgroup `P` of `C`.
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hP⟩
  -- `d = [P : X]` divides the odd `[C : X]` and the `2`-power `|P|`, hence `d = 1`.
  have hdvd_idx : (Q.X.subgroupOf Q.C).relIndex (P : Subgroup ↥Q.C) ∣ Q.X.relIndex Q.C :=
    ⟨(P : Subgroup ↥Q.C).index, (relIndex_mul_index hP).symm⟩
  have hodd : ¬ 2 ∣ (Q.X.subgroupOf Q.C).relIndex (P : Subgroup ↥Q.C) :=
    fun h => Q.two_not_dvd_relIndex_C (h.trans hdvd_idx)
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  have hdvd_card := relIndex_dvd_card (Q.X.subgroupOf Q.C) (P : Subgroup ↥Q.C)
  rw [hm] at hdvd_card
  obtain ⟨j, _, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_card
  have hj0 : j = 0 := by
    by_contra h
    exact hodd (hjeq ▸ dvd_pow_self 2 h)
  rw [hj0, pow_zero] at hjeq
  exact relIndex_eq_one.mp hjeq

/-! ### The normal `2`-complement `H` of `C` (Burnside) -/

/-- `2` is the smallest prime factor of `|C|` (as `x ∈ C` has order `2ⁿ`). -/
theorem minFac_card_C : (Nat.card ↥Q.C).minFac = 2 := by
  have h2dvd : 2 ∣ Nat.card ↥Q.C := by
    have hx : Q.x ∈ Q.C := Q.x_mem_C
    have hoc : orderOf (⟨Q.x, hx⟩ : ↥Q.C) = 2 ^ Q.n := by
      have h := orderOf_injective Q.C.subtype Q.C.subtype_injective (⟨Q.x, hx⟩ : ↥Q.C)
      rw [← h]
      exact Q.hx_order
    have hdvd := orderOf_dvd_natCard (⟨Q.x, hx⟩ : ↥Q.C)
    rw [hoc] at hdvd
    exact dvd_trans (dvd_pow_self 2 (by have := Q.hn; omega)) hdvd
  have hne1 : Nat.card ↥Q.C ≠ 1 := by
    intro h
    rw [h] at h2dvd
    norm_num at h2dvd
  exact le_antisymm (Nat.minFac_le_of_dvd le_rfl h2dvd) (Nat.minFac_prime hne1).two_le

/-- **Burnside inside `C`** (Gorenstein p. 374, via Theorem 7.6.1): `C` has a normal
`2`-complement — a normal subgroup `K₀ ≤ C` of odd cardinality complementing the
cyclic Sylow `2`-subgroup `X`.  Packaged as: a normal subgroup whose membership is
*exactly* "odd order", which is what makes `H ⊴ N` automatic later. -/
theorem exists_normal_two_complement :
    ∃ K₀ : Subgroup ↥Q.C, K₀.Normal ∧ ¬ 2 ∣ Nat.card K₀ ∧
      (∀ c : ↥Q.C, c ∈ K₀ ↔ Odd (orderOf c)) ∧
      K₀ ⊔ Q.X.subgroupOf Q.C = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPX⟩ := Q.exists_sylow_C_eq
  haveI hXcyc : IsCyclic ↥Q.X := by
    rw [show Q.X = Subgroup.zpowers Q.x from rfl]
    exact ⟨⟨⟨Q.x, mem_zpowers Q.x⟩, by
      rintro ⟨g, k, rfl⟩
      exact ⟨k, by ext; simp⟩⟩⟩
  haveI hcyc : IsCyclic (P : Subgroup ↥Q.C) := by
    rw [hPX]
    exact isCyclic_of_surjective (subgroupOfEquivOfLe Q.X_le_C).symm.toMonoidHom
      (subgroupOfEquivOfLe Q.X_le_C).symm.surjective
  have hcompl := IsCyclic.isComplement' Q.minFac_card_C hcyc
  set K₀ := (MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer Q.minFac_card_C)).ker
    with hK₀
  have hK₀card : Nat.card K₀ = (P : Subgroup ↥Q.C).index := hcompl.index_eq_card.symm
  have hK₀odd : ¬ 2 ∣ Nat.card K₀ := by rw [hK₀card]; exact P.not_dvd_index
  have hK₀idx : K₀.index = Nat.card (P : Subgroup ↥Q.C) := hcompl.symm.index_eq_card
  have hmem : ∀ c : ↥Q.C, c ∈ K₀ ↔ Odd (orderOf c) := by
    intro c
    constructor
    · -- elements of the odd-order group `K₀` have odd order
      intro hc
      have h1 : orderOf c = orderOf (⟨c, hc⟩ : K₀) :=
        orderOf_injective K₀.subtype K₀.subtype_injective ⟨c, hc⟩
      have hdvd : orderOf c ∣ Nat.card K₀ := by
        rw [h1]; exact orderOf_dvd_natCard _
      rw [Nat.odd_iff]
      rcases Nat.even_or_odd (orderOf c) with he | ho
      · exact absurd (he.two_dvd.trans hdvd) hK₀odd
      · exact Nat.odd_iff.mp ho
    · -- an odd-order element maps to `1` in the `2`-group `C⧸K₀`
      intro hodd
      obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
      have h2 : orderOf ((QuotientGroup.mk' K₀) c) ∣ orderOf c := orderOf_map_dvd _ c
      have h3 : orderOf ((QuotientGroup.mk' K₀) c) ∣ 2 ^ m := by
        have hdvd := orderOf_dvd_natCard ((QuotientGroup.mk' K₀) c)
        rwa [show Nat.card (↥Q.C ⧸ K₀) = 2 ^ m from by rw [← hm, ← hK₀idx]; rfl] at hdvd
      obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
      have hj0 : j = 0 := by
        by_contra h
        have h2div : (2 : ℕ) ∣ orderOf c := (hj ▸ dvd_pow_self 2 h).trans h2
        have hmod := Nat.odd_iff.mp hodd
        omega
      have hone : orderOf ((QuotientGroup.mk' K₀) c) = 1 := by rw [hj, hj0, pow_zero]
      exact (QuotientGroup.eq_one_iff c).mp (orderOf_eq_one_iff.mp hone)
  exact ⟨K₀, inferInstance, hK₀odd, hmem, by
    have := hcompl.sup_eq_top
    rwa [hPX] at this⟩

/-! ### `H` as a subgroup of `G`, and Lemma 1.2 (ii): `C = XH` -/

/-- **`H`** (Gorenstein Lemma 1.2): the normal `2`-complement of `C`, as a subgroup of
`G`.  Its membership predicate is canonical — "lies in `C` and has odd order"
(`mem_H_iff`) — so nothing depends on the choice of Burnside complement. -/
noncomputable def H : Subgroup G :=
  Q.exists_normal_two_complement.choose.map Q.C.subtype

/-- `H = {g ∈ C ∣ orderOf g is odd}`. -/
theorem mem_H_iff {g : G} : g ∈ Q.H ↔ g ∈ Q.C ∧ Odd (orderOf g) := by
  obtain ⟨-, -, hmem, -⟩ := Q.exists_normal_two_complement.choose_spec
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, ?_⟩
    have := (hmem c).mp hc
    rwa [← orderOf_injective Q.C.subtype Q.C.subtype_injective c] at this
  · rintro ⟨hgC, hgO⟩
    refine ⟨⟨g, hgC⟩, (hmem _).mpr ?_, rfl⟩
    have h1 : orderOf g = orderOf (⟨g, hgC⟩ : ↥Q.C) :=
      orderOf_injective Q.C.subtype Q.C.subtype_injective ⟨g, hgC⟩
    rwa [h1] at hgO

theorem H_le_C : Q.H ≤ Q.C := fun _ hg => (Q.mem_H_iff.mp hg).1

/-- `|H|` is odd. -/
theorem two_not_dvd_card_H : ¬ 2 ∣ Nat.card Q.H := by
  obtain ⟨-, hodd, -, -⟩ := Q.exists_normal_two_complement.choose_spec
  rwa [show Nat.card Q.H = Nat.card Q.exists_normal_two_complement.choose from
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ Q.C.subtype_injective).symm.toEquiv]

/-- Elements of `N` conjugate `C` into `C` (`C ⊴ N`, elementwise form). -/
theorem conj_mem_C_of_mem_N {n c : G} (hn : n ∈ Q.N) (hc : c ∈ Q.C) :
    n * c * n⁻¹ ∈ Q.C := by
  rw [C, mem_centralizer_iff] at hc ⊢
  intro t ht
  rw [N] at hn
  have ht' : n⁻¹ * t * n ∈ Q.T := by
    refine (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * t * n)).mpr ?_
    rwa [show n * (n⁻¹ * t * n) * n⁻¹ = t from by group]
  have h := hc _ ht'
  calc t * (n * c * n⁻¹) = n * (n⁻¹ * t * n * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * t * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * t := by group

/-- **`H ⊴ N`, elementwise form** (Gorenstein Lemma 1.2(i)): conjugation by `N`
preserves membership in `C` and the order, hence preserves `H`. -/
theorem conj_mem_H_of_mem_N {n h : G} (hn : n ∈ Q.N) (hh : h ∈ Q.H) :
    n * h * n⁻¹ ∈ Q.H := by
  obtain ⟨hhC, hhO⟩ := Q.mem_H_iff.mp hh
  refine Q.mem_H_iff.mpr ⟨Q.conj_mem_C_of_mem_N hn hhC, ?_⟩
  have h1 : orderOf ((MulAut.conj n) h) = orderOf h :=
    orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective h
  rwa [show n * h * n⁻¹ = (MulAut.conj n) h from rfl, h1]

/-- **Gorenstein Lemma 1.2 (ii): `C = XH`** (join form). -/
theorem X_sup_H_eq_C : Q.X ⊔ Q.H = Q.C := by
  obtain ⟨-, -, -, hsup⟩ := Q.exists_normal_two_complement.choose_spec
  have h := congrArg (Subgroup.map Q.C.subtype) hsup
  have htop : Subgroup.map Q.C.subtype ⊤ = Q.C := by
    rw [← MonoidHom.range_eq_map]
    exact Q.C.range_subtype
  rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_of_le_left Q.X_le_C, htop] at h
  rw [sup_comm]
  exact h

end QuaternionSylowSetup

end OddOrder.GroupTheory
