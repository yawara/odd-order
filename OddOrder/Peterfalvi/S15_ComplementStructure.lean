/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_Gate3

/-!
# Complement / maximal-subgroup structure for Peterfalvi §13 (13.17.c)/(13.19.c1)

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT` (2000-line limit, issue 0102):
the intersection structure `E ∩ Q = W₁` / `E ⊄ Q` / `|E| = pq`, the type-I/II
over-normalizer Frobenius data, the `E ∩ P` dichotomy, `E ≤ PW₁`, the `P ⋊ W₁`
structure, and the structural dichotomy `|M : M_F| ∈ {p, pq}`.
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.17.c), `E ∩ Q = W₁`** (Pf p.82) — the proven half of the §13 intersection
structure.  `W₁ ≤ E ⊓ Q` from `hW1E` and `W1_le_Q` ((13.2.b) `T`-side).  Conversely `E ⊓ Q` is a
`q`-subgroup of the elementary abelian `Q` (`Q_elementaryAbelian_T`, (13.2.a) `T`-side) sitting
inside the odd-order Frobenius complement `E`, which is a Z-group ([BG] Prop 3.9 via
Isaacs 6.9–6.11, `isZGroup_complement_of_isFrobeniusGroup_of_odd`); so `E ⊓ Q` is cyclic
(`IsPGroup.isCyclic_of_isZGroup`), and a cyclic group of exponent `q` has order dividing `q` —
with `|W₁| = q` from below, equality. -/
theorem complement_inf_Q_eq_W1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ⊓ hyp.Q = hyp.W1 := by
  classical
  set Em := frob.complement.map L.subtype with hEm
  have hW1le : hyp.W1 ≤ Em ⊓ hyp.Q := le_inf hW1E (W1_le_Q hG hyp)
  -- `E` is a Z-group (odd Frobenius complement), and `Em ≅ E`.
  have hodd : Odd (Nat.card ↥frob.complement) := hG.odd.of_dvd_nat
    ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card L))
  haveI hZE : _root_.IsZGroup ↥frob.complement :=
    OddOrder.Isaacs.Ch06.isZGroup_complement_of_isFrobeniusGroup_of_odd frob.frobenius hodd
  haveI hZEm : _root_.IsZGroup ↥Em := _root_.IsZGroup.of_injective
    (f := ((Subgroup.equivMapOfInjective frob.complement L.subtype
      Subtype.coe_injective).symm : ↥Em ≃* ↥frob.complement).toMonoidHom)
    (MulEquiv.injective _)
  -- `R := (Em ⊓ Q)` realized inside `Em` is a `q`-group (exponent `q` from `Q` elem.-abelian)
  have hQeA := Q_elementaryAbelian_T hG hyp hTTypeII
  set R : Subgroup ↥Em := (Em ⊓ hyp.Q).subgroupOf Em with hRdef
  have hexp : ∀ x : ↥R, x ^ hyp.q = 1 := by
    intro x
    have hgQ : ((x : ↥Em) : G) ∈ hyp.Q := (Subgroup.mem_subgroupOf.mp x.2).2
    have hq1 := hQeA.2 (⟨((x : ↥Em) : G), hgQ⟩ : ↥hyp.Q)
    have hg1 : (((x : ↥Em) : G)) ^ hyp.q = 1 := by
      simpa using congrArg Subtype.val hq1
    apply Subtype.ext; apply Subtype.ext
    push_cast
    exact hg1
  have hpg : IsPGroup hyp.q ↥R := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  haveI hFq : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  haveI hcyc : IsCyclic ↥R := hpg.isCyclic_of_isZGroup
  -- cyclic of exponent `q` ⟹ `|E ⊓ Q| ∣ q`
  obtain ⟨g, hgen⟩ := hcyc.exists_generator
  have hgq : g ^ hyp.q = 1 := hexp g
  have hcard_dvd : Nat.card ↥R ∣ hyp.q := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hgen]
    exact orderOf_dvd_of_pow_eq_one hgq
  have hcardR : Nat.card ↥(Em ⊓ hyp.Q) = Nat.card ↥R :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Em ⊓ hyp.Q ≤ Em)).toEquiv).symm
  -- `q = |W₁| ≤ |E ⊓ Q|` and `|E ⊓ Q| ∣ q` force `|E ⊓ Q| = q`
  have hqle : hyp.q ≤ Nat.card ↥(Em ⊓ hyp.Q) := by
    rw [hyp.q_eq_card_W1]
    exact Subgroup.card_le_of_le hW1le
  have hcard_eq : Nat.card ↥(Em ⊓ hyp.Q) = hyp.q :=
    le_antisymm (hcardR ▸ Nat.le_of_dvd hyp.q_prime.pos hcard_dvd) hqle
  exact (Subgroup.eq_of_le_of_card_ge hW1le
    (by rw [hcard_eq, hyp.q_eq_card_W1])).symm

/-- `W₁` (order `q`) is coprime to the type-I Frobenius kernel `L_F` (`q ∤ |L_F|`).  This is
Peterfalvi's "`W₁ ∩ H = 1`", from (8.17.a).

*Proof.*  `L` is type I while `S` and `T` are type non-I maximal subgroups, so `L` is conjugate to
neither (`not_conj_of_isTypeI_of_isTypeNonI`).  Hence (8.17.a) `card_LF_coprime_pq` gives
`|L_F| ⟂ p q`, in particular `|L_F| ⟂ q`, i.e. `q ∤ |L_F|`; the kernel `H = frob.typeI.typeF.H`
equals `L_F = maxNilpotentNormalHall L` (`TypeFData.H_eq`, so the "kernel_eq_MF" identification is
*not* opaque) and `|H.subgroupOf L| = |H|`.  The only gated input is `card_LF_coprime_pq` (B2,
BG Theorem E, owner F). -/
theorem q_not_dvd_kernel [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L) :
    ¬ hyp.q ∣ Nat.card ↥(frob.typeI.typeF.H.subgroupOf L) := by
  -- `L` is type I, while `S`, `T` are type non-I maximal: `L` is conjugate to neither.
  have hnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.S_maximal hyp.S_nonI
  have hnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.T_maximal hyp.T_nonI
  -- (8.17.a): `|L_F| ⟂ p q`, hence `q ∤ |L_F|`.
  have hcop := card_LF_coprime_pq _hG hyp hLmax hLI hnconjS hnconjT
  have hcopq : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.q :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left hyp.q hyp.p) hcop
  have hnotdvd : ¬ hyp.q ∣ Nat.card ↥(maxNilpotentNormalHall L) :=
    hyp.q_prime.coprime_iff_not_dvd.mp hcopq.symm
  -- `H = L_F = maxNilpotentNormalHall L`, and `|H.subgroupOf L| = |H|`.
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hHleL : frob.typeI.typeF.H ≤ L := by
    rw [hHeq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleL).toEquiv, hHeq]
  exact hnotdvd

/-- (13.17.a/b)-strengthening of (12.7): the type-I Frobenius decomposition of `L` can be taken
with the complement containing `W₁` — Peterfalvi's "let `E` be a complement to `H` in `L` such
that `W₁ ⊂ E`".  Since `W₁ ≤ N_G(U) ≤ L` is coprime to the kernel (`q ∤ |L_F|`,
`q_not_dvd_kernel`), Schur–Zassenhaus complement conjugacy
(`exists_conj_le_of_isComplement'_of_coprime`) places `W₁` in a conjugate `E₀^x` of any complement
`E₀`, which is again a Frobenius complement (`IsFrobeniusGroup.conjComplement`).  The only `sorry`
is the coprimality, gated on the opaque `kernel_eq_MF` carrier. -/
theorem exists_typeIFrobeniusData_W1_le [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLtypeI : IsTypeI L) (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    ∃ frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L, frob.kernel_eq_MF ∧
      hyp.W1 ≤ frob.complement.map L.subtype := by
  obtain ⟨frob₀, hker₀⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hnoV hLmax hLtypeI
  have hW1L : hyp.W1 ≤ L := hyp.W1_normalizes_U.trans hNUL
  haveI : (frob₀.typeI.typeF.H.subgroupOf L).Normal := frob₀.frobenius.isNormal
  -- `L` (maximal) is solvable, hence so is the kernel.
  haveI hLsolv : IsSolvable ↥L :=
    _hG.solvable_of_lt_top L (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hLmax).1)
  haveI : IsSolvable ↥(frob₀.typeI.typeF.H.subgroupOf L) := inferInstance
  -- coprimality `|W₁| = q` to `|L_F|`.
  have hcop : Nat.Coprime (Nat.card ↥(hyp.W1.subgroupOf L))
      (Nat.card ↥(frob₀.typeI.typeF.H.subgroupOf L)) := by
    have hW1card : Nat.card ↥(hyp.W1.subgroupOf L) = hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1L).toEquiv]
      exact hyp.q_eq_card_W1.symm
    rw [hW1card]
    exact (hyp.q_prime.coprime_iff_not_dvd).mpr (q_not_dvd_kernel _hG hyp hLmax hLtypeI frob₀)
  -- `W₁` lies in a conjugate `E₀^x` of the complement.
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    inferInstance frob₀.frobenius.isComplement hcop
  refine ⟨{ frob₀ with
      complement := frob₀.complement.map (MulAut.conj x).toMonoidHom
      frobenius := frob₀.frobenius.conjComplement x }, frob₀.kernel_eq_MF_holds, ?_⟩
  -- `W₁ = (W₁.subgroupOf L).map L.subtype ≤ (E₀^x).map L.subtype`.
  have : hyp.W1 = (hyp.W1.subgroupOf L).map L.subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le hW1L]
  rw [this]
  exact Subgroup.map_mono hx

/-- **`T`-side dual of `q_not_dvd_kernel`** (V-side): `p = |W₂|` is coprime to the type-I Frobenius
kernel `L_F` (`p ∤ |L_F|`).  Mirror; same gated input `card_LF_coprime_pq` (`|L_F| ⟂ pq`). -/
theorem p_not_dvd_kernel [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L) :
    ¬ hyp.p ∣ Nat.card ↥(frob.typeI.typeF.H.subgroupOf L) := by
  have hnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.S_maximal hyp.S_nonI
  have hnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.T_maximal hyp.T_nonI
  have hcop := card_LF_coprime_pq _hG hyp hLmax hLI hnconjS hnconjT
  have hcopp : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.p :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right hyp.p hyp.q) hcop
  have hnotdvd : ¬ hyp.p ∣ Nat.card ↥(maxNilpotentNormalHall L) :=
    hyp.p_prime.coprime_iff_not_dvd.mp hcopp.symm
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hHleL : frob.typeI.typeF.H ≤ L := by
    rw [hHeq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleL).toEquiv, hHeq]
  exact hnotdvd

/-- **`T`-side dual of `exists_typeIFrobeniusData_W1_le`** (V-side): the type-I Frobenius
decomposition of `L` can be taken with the complement containing `W₂` (`|W₂| = p` coprime to the
kernel by `p_not_dvd_kernel`, Schur–Zassenhaus complement conjugacy). -/
theorem exists_typeIFrobeniusData_W2_le [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLtypeI : IsTypeI L) (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    ∃ frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L, frob.kernel_eq_MF ∧
      hyp.W2 ≤ frob.complement.map L.subtype := by
  obtain ⟨frob₀, hker₀⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hnoV hLmax hLtypeI
  have hW2L : hyp.W2 ≤ L := hyp.W2_normalizes_V.trans hNVL
  haveI : (frob₀.typeI.typeF.H.subgroupOf L).Normal := frob₀.frobenius.isNormal
  haveI hLsolv : IsSolvable ↥L :=
    _hG.solvable_of_lt_top L (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hLmax).1)
  haveI : IsSolvable ↥(frob₀.typeI.typeF.H.subgroupOf L) := inferInstance
  have hcop : Nat.Coprime (Nat.card ↥(hyp.W2.subgroupOf L))
      (Nat.card ↥(frob₀.typeI.typeF.H.subgroupOf L)) := by
    have hW2card : Nat.card ↥(hyp.W2.subgroupOf L) = hyp.p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2L).toEquiv]
      exact hyp.p_eq_card_W2.symm
    rw [hW2card]
    exact (hyp.p_prime.coprime_iff_not_dvd).mpr (p_not_dvd_kernel _hG hyp hLmax hLtypeI frob₀)
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    inferInstance frob₀.frobenius.isComplement hcop
  refine ⟨{ frob₀ with
      complement := frob₀.complement.map (MulAut.conj x).toMonoidHom
      frobenius := frob₀.frobenius.conjComplement x }, frob₀.kernel_eq_MF_holds, ?_⟩
  have : hyp.W2 = (hyp.W2.subgroupOf L).map L.subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le hW2L]
  rw [this]
  exact Subgroup.map_mono hx

/-- **Peterfalvi (13.17.c), V-side dual — faithful dichotomy form, proven** (hub issue 3004,
ruling 3): for the `W₂`-containing Frobenius complement `E` of the type-I maximal `L` over
`N_G(V)`, either `E = W₂` (the `L = H ⋊ W₂` branch, `e = p`), or `E ⊓ P = W₂` and `E ⊄ P` (the
`L = H ⋊ (W₂W₁^y)` branch, leading to `e = pq`).  Unlike the S-side
(`complement_inf_Q_eq_W1`/`complement_not_le_Q`, whose small branch is excluded by (14.5)), both
branches are live here; the resolution to `e = pq` happens only inside (14.11).

*Proof.*  `E ⊓ P = W₂` holds unconditionally, by the mirror of `complement_inf_Q_eq_W1`:
`W₂ ≤ E ⊓ P` (`hW2E` + `W2_le_P`), and conversely `E ⊓ P` is a `p`-subgroup of the elementary
abelian `P` (`P_elementaryAbelian`, (13.2.a)) inside the Z-group `E`
(`isZGroup_complement_of_isFrobeniusGroup_of_odd`), hence cyclic of exponent `p`, so of order
`p = |W₂|`.  The dichotomy is then `by_cases` on `E ≤ P`: if so, `E = E ⊓ P = W₂`. -/
theorem complement_inf_P_structure_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype = hyp.W2 ∨
      (frob.complement.map L.subtype ⊓ hyp.P = hyp.W2 ∧
        ¬ frob.complement.map L.subtype ≤ hyp.P) := by
  classical
  set Em := frob.complement.map L.subtype with hEm
  have hInf : Em ⊓ hyp.P = hyp.W2 := by
    have hW2le : hyp.W2 ≤ Em ⊓ hyp.P := le_inf hW2E (W2_le_P _hG hyp)
    have hodd : Odd (Nat.card ↥frob.complement) := _hG.odd.of_dvd_nat
      ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card L))
    haveI hZE : _root_.IsZGroup ↥frob.complement :=
      OddOrder.Isaacs.Ch06.isZGroup_complement_of_isFrobeniusGroup_of_odd frob.frobenius hodd
    haveI hZEm : _root_.IsZGroup ↥Em := _root_.IsZGroup.of_injective
      (f := ((Subgroup.equivMapOfInjective frob.complement L.subtype
        Subtype.coe_injective).symm : ↥Em ≃* ↥frob.complement).toMonoidHom)
      (MulEquiv.injective _)
    have hPeA := hyp.P_elementaryAbelian _hG
    set R : Subgroup ↥Em := (Em ⊓ hyp.P).subgroupOf Em with hRdef
    have hexp : ∀ x : ↥R, x ^ hyp.p = 1 := by
      intro x
      have hgP : ((x : ↥Em) : G) ∈ hyp.P := (Subgroup.mem_subgroupOf.mp x.2).2
      have hp1 := hPeA.2 (⟨((x : ↥Em) : G), hgP⟩ : ↥hyp.P)
      have hg1 : (((x : ↥Em) : G)) ^ hyp.p = 1 := by
        simpa using congrArg Subtype.val hp1
      apply Subtype.ext; apply Subtype.ext
      push_cast
      exact hg1
    have hpg : IsPGroup hyp.p ↥R := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
    haveI hFp : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
    haveI hcyc : IsCyclic ↥R := hpg.isCyclic_of_isZGroup
    obtain ⟨g, hgen⟩ := hcyc.exists_generator
    have hcard_dvd : Nat.card ↥R ∣ hyp.p := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hgen]
      exact orderOf_dvd_of_pow_eq_one (hexp g)
    have hcardR : Nat.card ↥(Em ⊓ hyp.P) = Nat.card ↥R :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Em ⊓ hyp.P ≤ Em)).toEquiv).symm
    have hple : hyp.p ≤ Nat.card ↥(Em ⊓ hyp.P) := by
      rw [hyp.p_eq_card_W2]
      exact Subgroup.card_le_of_le hW2le
    have hcard_eq : Nat.card ↥(Em ⊓ hyp.P) = hyp.p :=
      le_antisymm (hcardR ▸ Nat.le_of_dvd hyp.p_prime.pos hcard_dvd) hple
    exact (Subgroup.eq_of_le_of_card_ge hW2le
      (by rw [hcard_eq, hyp.p_eq_card_W2])).symm
  by_cases hle : Em ≤ hyp.P
  · left
    rw [← hInf, inf_eq_left.mpr hle]
  · right
    exact ⟨hInf, hle⟩

/-- **`S`-side dual of `complement_le_QW2`** (V-side Huppert step): the `W₂`-containing Frobenius
complement `E` satisfies `E ≤ P W₁`.  Mirror of `complement_le_QW2` with `W₁/Q ↔ W₂/P`: `W₂` (of
prime order `p`) is normal in the Frobenius complement `E` (Huppert V.8.18b,
`normal_of_card_prime_of_isFrobeniusGroup_of_odd`), so `E ≤ N_G(W₂)`, and (13.16) `normalizer_W2`
gives `N_G(W₂) = P ⊔ W₁`.  (The Frobenius/Wielandt content of (13.16) is isolated in
`normalizer_W2_structure`.) -/
theorem complement_le_PW1 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ≤ hyp.P ⊔ hyp.W1 := by
  set E := frob.complement with hEdef
  -- `W₂ ≤ L`, and `W₂` (as a subgroup of `↥L`) is contained in `E`.
  have hEleL : E.map L.subtype ≤ L := Subgroup.map_subtype_le E
  have hW2L : hyp.W2 ≤ L := hW2E.trans hEleL
  have hW2L_le_E : hyp.W2.subgroupOf L ≤ E := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨e, he, hee⟩ := hW2E hx
    have hex : e = x := Subtype.coe_injective (by simpa using hee)
    rw [← hex]; exact he
  -- `R := W₂` viewed inside `E`, of prime order `p`.
  set R : Subgroup ↥E := (hyp.W2.subgroupOf L).subgroupOf E with hRdef
  have hRcard : Nat.card ↥R = hyp.p := by
    rw [hRdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2L_le_E).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2L).toEquiv]
    exact hyp.p_eq_card_W2.symm
  have hEdvd : Nat.card ↥E ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card E).trans (Subgroup.card_subgroup_dvd_card L)
  have hodd : Odd (Nat.card ↥E) := _hG.odd.of_dvd_nat hEdvd
  -- Huppert V.8.18 b): `W₂` is normal in `E`, so `E` normalizes `W₂` in `↥L`.
  haveI hRnormal : R.Normal :=
    OddOrder.Isaacs.Ch06.normal_of_card_prime_of_isFrobeniusGroup_of_odd
      frob.frobenius hodd hyp.p_prime hRcard
  have hEnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hW2L_le_E).mp hRnormal
  -- Lift to `G`: `E.map L.subtype ≤ N_G(W₂)`.
  have hEN : E.map L.subtype ≤ Subgroup.normalizer (hyp.W2 : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have heN := hEnorm he
    rw [Subgroup.mem_normalizer_iff] at heN ⊢
    intro w
    constructor
    · intro hw
      have hwL : w ∈ L := hW2L hw
      have hw' : (⟨w, hwL⟩ : ↥L) ∈ hyp.W2.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; exact hw
      have hconj := ((heN ⟨w, hwL⟩).mp hw')
      rw [Subgroup.mem_subgroupOf] at hconj
      simpa using hconj
    · intro hw
      have he' : (L.subtype e : G) ∈ L := e.2
      have hwL : w ∈ L := by
        have hrw : w = (L.subtype e)⁻¹ * ((L.subtype e) * w * (L.subtype e)⁻¹) * (L.subtype e) := by
          group
        rw [hrw]
        exact L.mul_mem (L.mul_mem (L.inv_mem he') (hW2L hw)) he'
      have hconjmem : (e * ⟨w, hwL⟩ * e⁻¹) ∈ hyp.W2.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; simpa using hw
      have hfin := (heN ⟨w, hwL⟩).mpr hconjmem
      rw [Subgroup.mem_subgroupOf] at hfin
      simpa using hfin
  -- (13.16): `N_G(W₂) = C_G(W₂) = P W₁`.
  have h1316 := normalizer_W2 _hG hyp
  calc E.map L.subtype ≤ Subgroup.normalizer (hyp.W2 : Set G) := hEN
    _ = Subgroup.centralizer (hyp.W2 : Set G) := h1316.1
    _ = hyp.P ⊔ hyp.W1 := h1316.2

/-- **`S`-side of the (13.17.c) `W₁`-structure**: `W₁ ≤ N_G(P)`, `P ⊓ W₁ = ⊥`, and `q ∤ |P|`.

All three are ungated `S`-side facts: `W₁ ≤ S ≤ N_G(P)` (`P = S_F ⊴ S`); `P ⊓ W₁ ≤ M' ⊓ W₁ = ⊥`
(`P ≤ M' = derivedInG S`, `M_complement` disjointness); and `q ∤ |P|` from
`Coprime |P| |U ⋊ W₁|` (`coprime_card_P_card_UW1`) with `|W₁| = q ∣ |U ⋊ W₁|`. -/
theorem P_W1_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.W1 ≤ Subgroup.normalizer (hyp.P : Set G) ∧ hyp.P ⊓ hyp.W1 = ⊥ ∧
      ¬ hyp.q ∣ Nat.card ↥hyp.P := by
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hM'W1 : derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW1⟩
    have hxS : x ∈ hyp.S := hM'_le_S hxM'
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((derivedInG hyp.S).subgroupOf hyp.S) ⊓ (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  refine ⟨hW1_le_S.trans hS_norm_P, ?_, ?_⟩
  · rw [eq_bot_iff]; intro x hx
    obtain ⟨hxP, hxW1⟩ := Subgroup.mem_inf.mp hx
    have hxm : x ∈ derivedInG hyp.S ⊓ hyp.W1 := Subgroup.mem_inf.mpr ⟨hP_le_M' hxP, hxW1⟩
    rwa [hM'W1] at hxm
  · intro hq
    have hcop := coprime_card_P_card_UW1 hG hyp
    have hW1dvd : Nat.card ↥hyp.W1 ∣ Nat.card ↥(hyp.U ⊔ hyp.W1) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have hcopPW1 : Nat.Coprime (Nat.card ↥hyp.P) (Nat.card ↥hyp.W1) :=
      hcop.coprime_dvd_right hW1dvd
    rw [← hyp.q_eq_card_W1] at hcopPW1
    have hqdvd1 : hyp.q ∣ 1 := hcopPW1 ▸ Nat.dvd_gcd hq (dvd_refl hyp.q)
    exact hyp.q_prime.one_lt.ne' (Nat.dvd_one.mp hqdvd1)

/-- **The `e = pq` branch computation** (V-side): from the (13.17.c)-dual second-branch facts
`E ⊓ P = W₂` and `E ⊄ P`, the complement order is `p q`.  This is the sorry-free arithmetic core
of `complement_card_p_or_pq_V` (the faithful dichotomy form; the deprecated unconditional
`complement_card_eq_pq_V` family was deleted per hub issue 3004 ruling 3). -/
theorem complement_card_eq_pq_V_of_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype)
    (hInf : frob.complement.map L.subtype ⊓ hyp.P = hyp.W2)
    (hnle : ¬ frob.complement.map L.subtype ≤ hyp.P) :
    Nat.card ↥frob.complement = hyp.p * hyp.q := by
  set Em := frob.complement.map L.subtype with hEm
  set Hg := hyp.P ⊔ hyp.W1 with hHg
  have hEH : Em ≤ Hg := complement_le_PW1 _hG hyp frob hW2E
  obtain ⟨hWnorm, hdisj, _⟩ := P_W1_structure _hG hyp
  have hPleH : hyp.P ≤ Hg := le_sup_left
  have hInfCard : Nat.card ↥(Em ⊓ hyp.P) = hyp.p := by rw [hInf]; exact hyp.p_eq_card_W2.symm
  haveI hPnorm : (hyp.P.subgroupOf Hg).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleH).mpr (sup_le Subgroup.le_normalizer hWnorm)
  have hHcard : Nat.card ↥Hg = Nat.card ↥hyp.P * hyp.q := by
    have h := OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hWnorm
      (show hyp.W1 ⊓ hyp.P = ⊥ by rw [inf_comm]; exact hdisj)
    rw [hHg, sup_comm, h, ← hyp.q_eq_card_W1]
    exact mul_comm _ _
  have hPpos : 0 < Nat.card ↥hyp.P := Nat.card_pos
  have hindexH : (hyp.P.subgroupOf Hg).index = hyp.q := by
    have hmul := Subgroup.card_mul_index (hyp.P.subgroupOf Hg)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleH).toEquiv, hHcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left hPpos hmul
  have hdvd : hyp.P.relIndex Em ∣ hyp.q := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (H := hyp.P.subgroupOf Hg)
      (K := Em.subgroupOf Hg)
    rwa [Subgroup.relIndex_subgroupOf hEH, hindexH] at h1
  have hne1 : hyp.P.relIndex Em ≠ 1 := fun h => hnle (Subgroup.relIndex_eq_one.mp h)
  have hrel : hyp.P.relIndex Em = hyp.q :=
    (hyp.q_prime.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  have hEmcard : Nat.card ↥Em = hyp.p * hyp.q := by
    have hmul := Subgroup.card_mul_index (hyp.P.subgroupOf Em)
    rw [show (hyp.P.subgroupOf Em).index = hyp.q from hrel, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Em ⊓ hyp.P ≤ Em)).toEquiv,
      hInfCard] at hmul
    exact hmul.symm
  rw [show Nat.card ↥frob.complement = Nat.card ↥Em from
    Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv, hEmcard]

/-- **Peterfalvi (13.17.c), V-side dual — the complement-order dichotomy** (hub issue 3004,
ruling 3): the `W₂`-containing Frobenius complement of the type-I maximal `L` over `N_G(V)` has
order `p` (the `L = H ⋊ W₂` branch) or `p q` (the `L = H ⋊ (W₂W₁^y)` branch).  The faithful
V-side export: unlike the S-side, the small branch cannot be excluded before (14.11). -/
theorem complement_card_p_or_pq_V [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p ∨ Nat.card ↥frob.complement = hyp.p * hyp.q := by
  rcases complement_inf_P_structure_dichotomy _hG hyp frob hW2E with hW2 | ⟨hInf, hnle⟩
  · left
    rw [Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv, hW2]
    exact hyp.p_eq_card_W2.symm
  · exact Or.inr (complement_card_eq_pq_V_of_structure _hG hyp frob hW2E hInf hnle)

/-- **Frobenius index bridge** (Pf (14.11), structural): for a type-I maximal `M` with
`TypeIFrobeniusData`, the index `|M : M_F|` of the Fitting kernel equals the order of the Frobenius
complement.  Immediate from the complement structure `M = M_F ⋊ complement` (`IsComplement'`) and the
kernel identity `typeF.H = M_F`.  Supplies the `e = |M : K| = p q` half of `MHypothesis`
(`e_eq_index` + `complement_card_eq_pq`): combined with the V-side `complement_card_eq_pq` (`= p q`),
the Fitting-kernel index of the type-I maximal over `N_G(V)` is `p q`. -/
theorem typeIFrobenius_kernel_index_eq_complement {M : Subgroup G}
    (data : OddOrder.Peterfalvi.S14.TypeIFrobeniusData M) :
    ((maxNilpotentNormalHall M).subgroupOf M).index = Nat.card data.complement := by
  rw [← data.typeI.typeF.H_eq]
  exact data.frobenius.isComplement.symm.index_eq_card

/-- **Peterfalvi (14.10), structural foundation — faithful dichotomy form** (hub issue 3004,
ruling 3): for `T` of type II, there is a type-I maximal subgroup `M` over `N_G(V)` carrying a §14
`S14.Hypothesis`, with Fitting-kernel index `|M : M_F| = p` or `= p q` (the (13.17.c)-dual
complement dichotomy `complement_card_p_or_pq_V`; the resolution to `p q` happens only inside
(14.11): the `K ≠ V` branch by the (14.11.2) character argument, the `K = V` branch by excluding
`E = W₂` in the §14 context).  The restructured §16 `exists_MHypothesis` cites this form. -/
theorem exists_M_structural_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.T) :
    ∃ (M : Subgroup G) (_typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis M),
      M ∈ maximalSubgroups G ∧
        Subgroup.normalizer (hyp.V : Set G) ≤ M ∧
          (((maxNilpotentNormalHall M).subgroupOf M).index = hyp.p ∨
            ((maxNilpotentNormalHall M).subgroupOf M).index = hyp.p * hyp.q) := by
  obtain ⟨L, hLmax, hLtypeI, hNVL, _hVH⟩ :=
    exists_typeI_maximal_overNormalizer_V hG hnoV hyp hTII
  obtain ⟨frob, _hker, hW2E⟩ := exists_typeIFrobeniusData_W2_le hG hnoV hyp hLmax hLtypeI hNVL
  obtain ⟨typeIHyp⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis hG hLmax hLtypeI
  refine ⟨L, typeIHyp, hLmax, hNVL, ?_⟩
  rw [typeIFrobenius_kernel_index_eq_complement frob]
  exact complement_card_p_or_pq_V hG hyp frob hW2E

end OddOrder.Peterfalvi.S15
