/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults.TypeVSinger

/-!
# BG Theorem 15.7(e): the non-TI Fitting structure

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*,
Section 15 — Theorem 15.7, clause (e).

This leaf assembles clause `(e)` of BG Theorem 15.7 in the shape of the MathComp formalization
(`coq/theories/BGsection15.v`, `nonTI_Fitting_structure`, the `(*e*)` line of the statement):

```
(*e*) (*1*) [/\ M \in 'M_'F, abelian H & 'r(H) = 2]
   \/ let p := #|X| in [/\ prime p, ~~ abelian 'O_p(H), cyclic 'O_p^'(H)
    & (*2*) {in \pi(H), forall q, exponent (M / H) %| q.-1}
   \/ (*3*) [/\ #|'O_p(H)| = (p ^ 3)%N, M \in 'M_'P1 & #|M / H| %| p.+1] ]
```

Here `H = M_F` and `X = F(M) ∩ F(M)ᵍ` is the intersection witnessing the failure of the `TI`
property.  Note the bracketing, which the BG text prints less explicitly: the three conjuncts
`p = |X|` prime, `O_p(H)` non-abelian and `O_{p'}(H)` cyclic are **factored out** of `(e2)`/`(e3)`,
and `(e2) ∨ (e3)` is an *inner* disjunction.  In particular `(e2)` carries **no** type constraint —
it holds for type-`F` *and* for those type-`P₁` maximal subgroups whose `κ`-Hall subgroup satisfies
the Frobenius divisibility; only `(e3)` pins `M` to type `P₁`.

The mathematical content is already in place: the `(e1)` branch is `S15`'s abelian dichotomy, the
shared conjuncts come from the non-TI witness of `S15`, the `(e2)` type-`F` divisibility is the
Frobenius engine `typeF_exponent_dvd_sub_one_of_invariant_card`, and the type-`P₁` inner
disjunction is `typeP1_kappaHall_dvd_sub_one_or_singer_of_not_fittingIsTI`.  What this file adds
is the assembly plus the two *quotient bridges* that convert the internal complement presentations
(`M = M_F ⋊ U` for type `F`, `M = M_F ⋊ K` for type `P₁`) into BG's quotient `M / H`:

* `exponent_quotient_mf_eq_exponent_typeFData_U` — `exponent (M/M_F) = exponent U`;
* `index_mf_subgroupOf_eq_card_kappaHall` — `[M : M_F] = |K|`.
-/
namespace OddOrder.BG.Ch4.S16
open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open OddOrder.BG.Ch4.S15
open scoped Pointwise

variable {G : Type*} [Group G]

/-- `M_F` is normal in `M`, as a `Normal` **instance** so that the quotient `M ⧸ M_F` of BG
Theorem 15.7(e) elaborates.  The proof is `maxNilpotentNormalHall_subgroupOf_normal` (a `theorem`
in `S15`, hence not available to typeclass synthesis). -/
instance maxNilpotentNormalHall_subgroupOf_normal_instance (M : Subgroup G) :
    ((maxNilpotentNormalHall M).subgroupOf M).Normal :=
  maxNilpotentNormalHall_subgroupOf_normal M

/-- **Quotient bridge, type `F`** (BG Theorem 15.7(e2), Coq `exponent (M / H)`): for a type-`F`
datum `td` on `M` the quotient `M / M_F` is isomorphic to the complement `U`, so the two exponents
agree.

`td.complement` is the internal statement `M = M_F ⋊ U` (as a complement of `subgroupOf`s inside
`↥M`); `Subgroup.IsComplement'.QuotientMulEquiv` turns it into `↥M ⧸ (M_F).subgroupOf M ≃* U`
once `M_F` is known normal in `M` (the instance above), and
`Subgroup.subgroupOfEquivOfLe td.U_le` identifies `U.subgroupOf M` with `U`.  This is what lets the
`(e2)` divisibility be *stated* on BG's quotient `M/H` while being *proved* on the complement, where
the Frobenius action of `td.U0` lives. -/
theorem exponent_quotient_mf_eq_exponent_typeFData_U [Finite G] {M : Subgroup G}
    (td : OddOrder.GroupTheory.TypeFData M) :
    Monoid.exponent (↥M ⧸ (MF M).subgroupOf M) = Monoid.exponent ↥td.U := by
  have hMFH : MF M = td.H := td.H_eq.symm
  have hcompl : Subgroup.IsComplement' ((MF M).subgroupOf M) (td.U.subgroupOf M) := by
    rw [hMFH]; exact td.complement
  exact Monoid.exponent_eq_of_mulEquiv
    (hcompl.symm.QuotientMulEquiv.trans (Subgroup.subgroupOfEquivOfLe td.U_le))

/-- **Quotient bridge, type `P₁`** (BG Theorem 15.7(e2)/(e3), Coq `#|M / H|`): for a type-`P₁`
maximal `M` with `M_F = M_σ` and a cyclic `κ`-Hall subgroup `K`, the index `[M : M_F]` is `|K|`.

For type `P₁` one has `M' = M_σ = M_F` (`isTypeP1_derivedInG_eq_Msigma` together with `hmf`), and
`K` complements `M'` in `M` (Theorem 14.7(h) duality), so the index of `M_F` is the order of `K`
(`card_kappaHall_eq_derived_index`). -/
theorem index_mf_subgroupOf_eq_card_kappaHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) [IsCyclic ↥K]
    (hmf : MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    ((MF M).subgroupOf M).index = Nat.card ↥K := by
  rw [hmf, ← isTypeP1_derivedInG_eq_Msigma hG hM hP1]
  exact (card_kappaHall_eq_derived_index hG hM hP1.1 hKM hK).symm

/-- **BG Theorem 15.7(e)** (Coq `BGsection15.nonTI_Fitting_structure`, clause `(*e*)`): let `M` be a
maximal subgroup of the minimal simple group `G` of odd order whose Fitting subgroup is *not* `TI`,
and let `g ∉ M` be such that the witness `X = F(M) ⊓ F(M)ᵍ` is nontrivial.  Then either

* **(e1)** `M` is of type `F`, `H = M_F` is abelian and `r(H) = 2`; or
* `p = |X|` is prime, `O_p(H)` is non-abelian, `O_{p'}(H)` is cyclic, and moreover
  * **(e2)** `exponent (M/H) ∣ q − 1` for every `q ∈ π(H)`, or
  * **(e3)** `|O_p(H)| = p³`, `M` is of type `P₁` and `[M : H] ∣ p + 1`.

⚠ The bracketing is BG's (and Coq's): the three conjuncts about `p`, `O_p(H)` and `O_{p'}(H)` are
shared, and `(e2) ∨ (e3)` is an inner disjunction.  `(e2)` carries **no** type constraint — a
type-`P₁` maximal subgroup whose `κ`-Hall subgroup satisfies the Frobenius divisibility lands in
`(e2)`, not `(e3)`; only `(e3)` forces type `P₁`.

Proof.  Split on whether `M_F` is abelian.

* Abelian: `S15.isTypeF_of_isMulCommutative_mf_of_not_fittingIsTI` gives type `F` and
  `S15.rank_mf_eq_two_of_isMulCommutative_of_not_fittingIsTI` the rank, i.e. `(e1)`.
* Non-abelian: the non-TI witness `X₁ ≤ X` of order `p`
  (`exists_orderP_witness_of_inf_conj_fitting_ne_bot`) gives `p = |X|`
  (`card_inf_conj_fitting_eq_of_not_isMulCommutative`, BG p. 121 l. 7 via Lemma 10.13(b)), the
  non-abelian `O_p(M_F)` (`opiCore_singleton_not_isMulCommutative_of_witness`) and the cyclic
  `O_{p'}(M_F)` (`typeF_nonabelian_cyclic_opiCore_compl`, Coq `cycHp'`).  For the inner
  disjunction, `fitting_not_ti_cases` splits `M` into type `F` or type `P₁`:
  * type `F`: `(e2)`, by the Frobenius divisibility `typeF_exponent_dvd_sub_one_of_invariant_card`
    applied to the per-prime `M`-normal order-`q` witnesses
    (`exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`), transported to `M/H` by
    `exponent_quotient_mf_eq_exponent_typeFData_U`;
  * type `P₁`: `typeP1_kappaHall_dvd_sub_one_or_singer_of_not_fittingIsTI` produces exactly the
    inner disjunction in terms of `|K|`, and `index_mf_subgroupOf_eq_card_kappaHall` rewrites `|K|`
    as `[M : H]` (for `(e2)` via `exponent (M/H) ∣ |M/H| = [M : H] = |K|`). -/
theorem fitting_not_ti_structure_e [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ S15.FittingIsTI M) {g : G} (hgM : g ∉ M)
    (hXne : (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) ≠ ⊥) :
    (S14.IsTypeF M ∧ IsMulCommutative ↥(S15.MF M) ∧ rank ↥(S15.MF M) = 2) ∨
    (∃ p : ℕ, p.Prime ∧
      Nat.card ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) = p ∧
      ¬ IsMulCommutative ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) ∧
      IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (S15.MF M)) ∧
      ((∀ q ∈ (Nat.card ↥(S15.MF M)).primeFactors,
          Monoid.exponent (↥M ⧸ (S15.MF M).subgroupOf M) ∣ q - 1) ∨
       (Nat.card ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) = p ^ 3 ∧ S14.IsTypeP1 M ∧
          ((S15.MF M).subgroupOf M).index ∣ p + 1))) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  by_cases habel : IsMulCommutative ↥(S15.MF M)
  · -- **(e1)**: `M_F` abelian ⟹ `M` is of type `F` and `r(M_F) = 2`.
    exact Or.inl ⟨S15.isTypeF_of_isMulCommutative_mf_of_not_fittingIsTI hG hM hnotTI habel, habel,
      S15.rank_mf_eq_two_of_isMulCommutative_of_not_fittingIsTI hG hM hnotTI habel⟩
  · -- `M_F` non-abelian: the shared conjuncts, then the inner `(e2)`/`(e3)` disjunction.
    obtain ⟨p, X₁, hp, hpσ, hX₁card, hX₁Mσ, -, hCGnotM, hrank3, hX₁X⟩ :=
      S15.exists_orderP_witness_of_inf_conj_fitting_ne_bot hG hM hgM hXne
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨hcases, hmf, -, -, -⟩ := S15.fitting_not_ti_cases hG hM hnotTI
    have hX₁MF : X₁ ≤ S15.MF M := hX₁Mσ.trans hmf.symm.le
    obtain ⟨hpπ, hcyc⟩ :=
      S15.typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM habel
    refine Or.inr ⟨p, hp,
      S15.card_inf_conj_fitting_eq_of_not_isMulCommutative hG hM hnotTI hgM hp hpσ hX₁card hX₁X
        hCGnotM hrank3 habel,
      S15.opiCore_singleton_not_isMulCommutative_of_witness hG hM hp hX₁card hX₁MF hCGnotM habel,
      hcyc, ?_⟩
    rcases hcases with hF | hP1
    · -- **type `F` ⟹ (e2)**: the Frobenius divisibility on the complement `U`, moved to `M/M_F`.
      obtain ⟨td⟩ := isTypeF_groupTheory_of_isTypeF hG hM hF
      refine Or.inl fun q hqπ => ?_
      have hq : q.Prime := Nat.prime_of_mem_primeFactors hqπ
      obtain ⟨Z, hZMF, hZcard, hMNZ, -, -⟩ :=
        S15.exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI hG hM hp hX₁card hX₁MF hCGnotM
          hrank3 habel hq hqπ
      rw [exponent_quotient_mf_eq_exponent_typeFData_U td]
      exact typeF_exponent_dvd_sub_one_of_invariant_card td (by rw [td.H_eq]; exact hZMF) hZcard
        ((td.U0_le.trans td.U_le).trans hMNZ)
    · -- **type `P₁`**: reconstruct the cyclic `κ`-Hall `K` and the trivial `(κ ∪ σ)'`-Hall `U`,
      -- then transport the `|K|`-form of the inner disjunction to BG's quotient `M/M_F`.
      obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
      set K : Subgroup G := K'.map M.subtype with hKdef
      have hKM : K ≤ M := Subgroup.map_subtype_le K'
      have hKeq : K.subgroupOf M = K' :=
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
      have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
      have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
          ((⊥ : Subgroup G).subgroupOf M) := by
        rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
        intro q hq
        simp only [Set.mem_compl_iff, not_not]
        by_cases hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M
        · exact Set.mem_union_right _ hqσ
        · exact Set.mem_union_left _ (hP1.2 ▸ ⟨hq, hqσ⟩)
      haveI hKcyc : IsCyclic ↥K := (typeP_auxiliary_structure hG hM hKM bot_le hK rfl hU).2.1
      have hindex : ((S15.MF M).subgroupOf M).index = Nat.card ↥K :=
        index_mf_subgroupOf_eq_card_kappaHall hG hM hP1 hKM hK hmf
      rcases typeP1_kappaHall_dvd_sub_one_or_singer_of_not_fittingIsTI hG hM hP1 hmf hKM hK hU
        hp hpσ hpπ hX₁card hX₁MF hCGnotM hrank3 habel with hdvd | ⟨hcube, hsucc⟩
      · -- inner-left `(e2)`: `exponent (M/M_F) ∣ |M/M_F| = [M : M_F] = |K| ∣ q − 1`.
        refine Or.inl fun q hqπ => ?_
        refine dvd_trans (dvd_trans Group.exponent_dvd_nat_card ?_) (hdvd q hqπ)
        rw [← Subgroup.index_eq_card, hindex]
      · -- inner-right `(e3)`: the Singer case, with `[M : M_F] = |K| ∣ p + 1`.
        exact Or.inr ⟨hcube, hP1, hindex ▸ hsucc⟩

end OddOrder.BG.Ch4.S16
