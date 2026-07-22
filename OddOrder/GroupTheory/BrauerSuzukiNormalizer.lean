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

/-! ### Lemma 1.2 (i): `N = SH` -/

theorem isCyclic_T : IsCyclic ↥Q.T := by
  rw [show Q.T = Subgroup.zpowers (Q.x ^ (2 : ℕ)) from rfl]
  exact ⟨⟨⟨Q.x ^ (2 : ℕ), mem_zpowers _⟩, by
    rintro ⟨g, k, rfl⟩
    exact ⟨k, by ext; simp⟩⟩⟩

theorem card_T : Nat.card ↥Q.T = 2 ^ (Q.n - 1) := by
  rw [show Q.T = Subgroup.zpowers (Q.x ^ (2 : ℕ)) from rfl, Nat.card_zpowers, orderOf_pow,
    Q.hx_order, Nat.gcd_eq_right (dvd_pow_self 2 (by have := Q.hn; omega)),
    show (2 : ℕ) ^ Q.n = 2 ^ (Q.n - 1) * 2 from by
      rw [← pow_succ]
      congr 1
      have := Q.hn
      omega,
    Nat.mul_div_cancel _ (by norm_num)]

/-- **Odd-order elements of `N` centralize `T`** (Gorenstein Lemma 1.2, via
Lemma 5.4.1): `N/C` embeds in `Aut(T)`, a `2`-group since `T` is a cyclic `2`-group. -/
theorem mem_C_of_odd_of_mem_N {g : G} (hgN : g ∈ Q.N) (hodd : Odd (orderOf g)) :
    g ∈ Q.C := by
  haveI := Q.isCyclic_T
  set φ : ↥Q.N →* MulAut ↥Q.T := Subgroup.normalizerMonoidHom Q.T with hφ
  have hker : φ ⟨g, hgN⟩ = 1 := by
    have h1 : orderOf g = orderOf (⟨g, hgN⟩ : ↥Q.N) :=
      orderOf_injective Q.N.subtype Q.N.subtype_injective ⟨g, hgN⟩
    have h2 : orderOf (φ ⟨g, hgN⟩) ∣ orderOf g := by
      rw [h1]
      exact orderOf_map_dvd φ _
    have h3 : orderOf (φ ⟨g, hgN⟩) ∣ 2 ^ (Q.n - 2) := by
      have hdvd := orderOf_dvd_natCard (φ ⟨g, hgN⟩)
      rwa [show Nat.card (MulAut ↥Q.T) = 2 ^ (Q.n - 2) from by
        rw [IsCyclic.card_mulAut, Q.card_T,
          Nat.totient_prime_pow Nat.prime_two (by have := Q.hn; omega),
          show Q.n - 1 - 1 = Q.n - 2 from by have := Q.hn; omega]
        norm_num] at hdvd
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    have hj0 : j = 0 := by
      by_contra h
      have h2div : (2 : ℕ) ∣ orderOf g := (hj ▸ dvd_pow_self 2 h).trans h2
      have := Nat.odd_iff.mp hodd
      omega
    exact orderOf_eq_one_iff.mp (by rw [hj, hj0, pow_zero])
  rw [C, mem_centralizer_iff]
  intro t ht
  have h4 := congrArg (fun ψ : MulAut ↥Q.T => ((ψ ⟨t, ht⟩ : ↥Q.T) : G)) hker
  simp only [MulAut.one_apply] at h4
  have h5 : ((φ ⟨g, hgN⟩ ⟨t, ht⟩ : ↥Q.T) : G) = g * t * g⁻¹ := rfl
  rw [h5] at h4
  calc t * g = (g * t * g⁻¹) * g := by rw [h4]
    _ = g * t := by group

/-- Odd-order elements of `N` lie in `H` (they centralize `T` and have odd order). -/
theorem mem_H_of_odd_of_mem_N {g : G} (hgN : g ∈ Q.N) (hodd : Odd (orderOf g)) :
    g ∈ Q.H :=
  Q.mem_H_iff.mpr ⟨Q.mem_C_of_odd_of_mem_N hgN hodd, hodd⟩

/-- `H ≤ N`. -/
theorem H_le_N : Q.H ≤ Q.N := Q.H_le_C.trans Q.C_le_N

/-- `H ⊴ N` (bundled form). -/
instance : (Q.H.subgroupOf Q.N).Normal := by
  refine ⟨?_⟩
  rintro ⟨h, hhN⟩ hh ⟨m, hmN⟩
  rw [mem_subgroupOf] at hh ⊢
  exact Q.conj_mem_H_of_mem_N hmN hh

/-- **Gorenstein Lemma 1.2 (i): `N = SH`** (join form).  The quotient `N/H` has no
element of odd prime order (its `p`-part would be an odd-order element of `N` outside
`H`), so the image of the Sylow `2`-subgroup `S` has index `1`. -/
theorem S_sup_H_eq_N : (Q.S : Subgroup G) ⊔ Q.H = Q.N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup ↥Q.N := Q.H.subgroupOf Q.N with hK
  set P' : Sylow 2 ↥Q.N := Q.S.subtype Q.S_le_N with hP'
  set π := QuotientGroup.mk' K with hπ
  -- no odd prime divides `|N ⧸ H|`
  have hodd_free : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card (↥Q.N ⧸ K) := by
    intro p hp hp2 hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fintype (↥Q.N ⧸ K) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at hdvd
    obtain ⟨gbar, hgbar⟩ := exists_prime_orderOf_dvd_card p hdvd
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K gbar
    have hdpos : (0 : ℕ) < orderOf y := orderOf_pos y
    have hpd : p ∣ orderOf y := by
      rw [← hgbar]
      exact orderOf_map_dvd π y
    -- `w = y^m` is the `p`-part of `y`: odd order, hence in `K`; but `π w ≠ 1`.
    set v := (orderOf y).factorization p with hv
    set m := orderOf y / p ^ v with hm
    have hmd : p ^ v * m = orderOf y := Nat.ordProj_mul_ordCompl_eq_self (orderOf y) p
    have hmdvd : m ∣ orderOf y := Dvd.intro_left _ hmd
    have hmpos : 0 < m := Nat.pos_of_mul_pos_left (a := p ^ v) (by rw [hmd]; exact hdpos)
    have hw : orderOf (y ^ m) = p ^ v := by
      rw [orderOf_pow, Nat.gcd_eq_right hmdvd, ← hmd, Nat.mul_div_cancel _ hmpos]
    have hvpos : 0 < v := hp.factorization_pos_of_dvd hdpos.ne' hpd
    have hwodd : Odd (orderOf (y ^ m)) := by
      rw [hw]
      exact (hp.odd_of_ne_two hp2).pow
    have hwK : y ^ m ∈ K := by
      rw [hK, mem_subgroupOf]
      refine Q.mem_H_of_odd_of_mem_N (y ^ m).2 ?_
      have h1 : orderOf ((y ^ m : ↥Q.N) : G) = orderOf (y ^ m) :=
        orderOf_injective Q.N.subtype Q.N.subtype_injective (y ^ m)
      rwa [h1]
    have hπw1 : π (y ^ m) = 1 := (QuotientGroup.eq_one_iff _).mpr hwK
    have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hdpos.ne'
    have hπwp : orderOf (π (y ^ m)) = p := by
      rw [map_pow, orderOf_pow, hgbar,
        (hp.coprime_iff_not_dvd.mpr hpm : Nat.gcd p m = 1), Nat.div_one]
    rw [hπw1, orderOf_one] at hπwp
    exact hp.one_lt.ne hπwp
  -- the image of the Sylow `2`-subgroup of `N` has index `1` in the quotient
  have hidx : ((P' : Subgroup ↥Q.N).map π).index = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hdvd
    rcases eq_or_ne p 2 with rfl | hp2
    · -- `2` cannot divide it: the index divides the odd index of the Sylow `P'`.
      have h1 : ((P' : Subgroup ↥Q.N).map π).index = ((P' : Subgroup ↥Q.N) ⊔ K).index := by
        rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K),
          Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      have h2 : ((P' : Subgroup ↥Q.N) ⊔ K).index ∣ (P' : Subgroup ↥Q.N).index :=
        Subgroup.index_dvd_of_le le_sup_left
      rw [h1] at hdvd
      exact P'.not_dvd_index (hdvd.trans h2)
    · -- an odd prime cannot divide it: it would divide `|N⧸H|`.
      exact hodd_free p hp hp2 (hdvd.trans (Subgroup.index_dvd_card _))
  have hmap_top : (P' : Subgroup ↥Q.N).map π = ⊤ := Subgroup.index_eq_one.mp hidx
  have hsup' : (P' : Subgroup ↥Q.N) ⊔ K = ⊤ := by
    have h := congrArg (Subgroup.comap π) hmap_top
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h
  -- transport to `G` along `N.subtype`
  have h := congrArg (Subgroup.map Q.N.subtype) hsup'
  have htopN : Subgroup.map Q.N.subtype ⊤ = Q.N := by
    rw [← MonoidHom.range_eq_map]
    exact Q.N.range_subtype
  rw [hP', Sylow.coe_subtype, hK, Subgroup.map_sup, subgroupOf_map_subtype,
    subgroupOf_map_subtype, htopN, inf_of_le_left Q.S_le_N, inf_of_le_left Q.H_le_N] at h
  exact h
