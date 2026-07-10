/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_Gate3

/-!
# TAIL

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-- **Peterfalvi (13.17.c) §13 intersection structure.**  The `W₁`-containing Frobenius complement
`E` of the type-I `L` meets `Q = T_F` exactly in `W₁` (Pf p.82 "`E ∩ Q = W₁`"), and is not
contained in `Q` (the `E = W₁` alternative is excluded by Peterfalvi (13.19.c1)/(13.2.a)).  This is
the genuine deep §13 structural datum behind the order `|E| = p q`; it is not reducible to the
existing §13 residuals (`TypeIFrobeniusData` carries no complement-order field).  `:= sorry`,
isolated — the order argument `complement_card_eq_pq` below is sorry-free modulo this. -/
theorem complement_inf_Q_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ⊓ hyp.Q = hyp.W1 ∧
      ¬ frob.complement.map L.subtype ≤ hyp.Q := sorry

/-- **Peterfalvi (13.17.c) order argument.**  The `W₁`-containing Frobenius complement `E` of `L`
has order `p q`.

*Proof (Pf p.82).*  `E ⊆ Q W₂` (`complement_le_QW2`), and `Q ⋊ W₂` has `Q ◁ Q W₂` with
`[Q W₂ : Q] = |W₂| = p` (`Q_W2_structure`).  The relative index `[E : E ∩ Q]` divides `[Q W₂ : Q] = p`
(normal-subgroup relative index, `relIndex_dvd_index_of_normal` inside `↥(Q W₂)`) and is `≠ 1` since
`E ⊄ Q`, hence `= p`; with `E ∩ Q = W₁` of order `q`, `|E| = |E ∩ Q| · [E : E ∩ Q] = q p`.  The two
§13 facts `E ∩ Q = W₁` and `E ⊄ Q` are isolated in `complement_inf_Q_structure`; everything else is
sorry-free group theory. -/
theorem complement_card_eq_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q := by
  set Em := frob.complement.map L.subtype with hEm
  set Hg := hyp.Q ⊔ hyp.W2 with hHg
  -- §13 residual: `E ∩ Q = W₁` and `E ⊄ Q`.
  obtain ⟨hInf, hnle⟩ := complement_inf_Q_structure _hG hyp frob hW1E
  -- `E ⊆ Q W₂` (Huppert step) and the `Q ⋊ W₂` structure.
  have hEH : Em ≤ Hg := complement_le_QW2 _hG hyp hTTypeII frob hW1E
  obtain ⟨hWnorm, hdisj, _⟩ := Q_W2_structure _hG hyp hTTypeII
  have hQleH : hyp.Q ≤ Hg := le_sup_left
  -- `|E ∩ Q| = |W₁| = q`.
  have hInfCard : Nat.card ↥(Em ⊓ hyp.Q) = hyp.q := by rw [hInf]; exact hyp.q_eq_card_W1.symm
  -- `Q ◁ Q W₂` (as `Q W₂ ≤ N_G(Q)`).
  haveI hQnorm : (hyp.Q.subgroupOf Hg).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleH).mpr (sup_le Subgroup.le_normalizer hWnorm)
  -- `|Q W₂| = |Q| · p`.
  have hHcard : Nat.card ↥Hg = Nat.card ↥hyp.Q * hyp.p := by
    have h := OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hWnorm
      (show hyp.W2 ⊓ hyp.Q = ⊥ by rw [inf_comm]; exact hdisj)
    rw [hHg, sup_comm, h, ← hyp.p_eq_card_W2]
    exact mul_comm _ _
  have hQpos : 0 < Nat.card ↥hyp.Q := Nat.card_pos
  -- `[Q W₂ : Q] = p`.
  have hindexH : (hyp.Q.subgroupOf Hg).index = hyp.p := by
    have hmul := Subgroup.card_mul_index (hyp.Q.subgroupOf Hg)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleH).toEquiv, hHcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left hQpos hmul
  -- `[E : E ∩ Q] = Q.relIndex E` divides `[Q W₂ : Q] = p`, and is `≠ 1` (`E ⊄ Q`), hence `= p`.
  have hdvd : hyp.Q.relIndex Em ∣ hyp.p := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (H := hyp.Q.subgroupOf Hg)
      (K := Em.subgroupOf Hg)
    rwa [Subgroup.relIndex_subgroupOf hEH, hindexH] at h1
  have hne1 : hyp.Q.relIndex Em ≠ 1 := fun h => hnle (Subgroup.relIndex_eq_one.mp h)
  have hrel : hyp.Q.relIndex Em = hyp.p :=
    (hyp.p_prime.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  -- `|E| = |E ∩ Q| · [E : E ∩ Q] = q · p`.
  have hEmcard : Nat.card ↥Em = hyp.q * hyp.p := by
    have hmul := Subgroup.card_mul_index (hyp.Q.subgroupOf Em)
    rw [show (hyp.Q.subgroupOf Em).index = hyp.p from hrel, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Em ⊓ hyp.Q ≤ Em)).toEquiv,
      hInfCard] at hmul
    exact hmul.symm
  -- transfer `|E.map| = |E|`.
  rw [show Nat.card ↥frob.complement = Nat.card ↥Em from
    Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv, hEmcard]
  exact mul_comm _ _

/-- **Peterfalvi (13.17.c)/(14.5)**: the `W₁`-containing Frobenius complement of the type-I
subgroup `L` over `N_G(U)` has order `p q` and contains a conjugate `W₂^y` (`y ∈ Q`).

Assembled from the order argument (`complement_card_eq_pq`, gated on `E ∩ Q = W₁`) and the
group-theoretic `∃ y` extraction (`exists_mem_conj_W2_le_of_dvd_card`, Schur–Zassenhaus), the
latter fed `E ⊆ Q W₂` by the Huppert step (`complement_le_QW2`).  The `W₁ ⊆ E` hypothesis records
Peterfalvi's choice "let `E` be a complement to `H` in `L` such that `W₁ ⊂ E`". -/
theorem typeI_overNormalizer_complement [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) (hTTypeII : IsTypeII hyp.T) {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q ∧
      ∃ y ∈ hyp.Q, (MulAut.conj y • hyp.W2 : Subgroup G) ≤
        frob.complement.map L.subtype := by
  have hcard := complement_card_eq_pq _hG hyp hTTypeII frob hW1E
  refine ⟨hcard, ?_⟩
  obtain ⟨hWnorm, hdisj, hpQ⟩ := Q_W2_structure _hG hyp hTTypeII
  have hEQW2 := complement_le_QW2 _hG hyp hTTypeII frob hW1E
  -- `Q` is solvable: `Q = T_F ≤ T < ⊤`.
  haveI hQsolv : IsSolvable ↥hyp.Q := by
    have hQT : hyp.Q ≤ hyp.T := by
      rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
    have hTlt : hyp.T < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1
    exact _hG.solvable_of_lt_top hyp.Q (lt_of_le_of_lt hQT hTlt)
  -- `p ∣ |E.map| = |E| = p q`.
  have hpE : hyp.p ∣ Nat.card ↥(frob.complement.map L.subtype) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv.symm, hcard]
    exact dvd_mul_right hyp.p hyp.q
  exact exists_mem_conj_W2_le_of_dvd_card hWnorm hQsolv hdisj hyp.p_prime
    hyp.p_eq_card_W2.symm hpQ hEQW2 hpE

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
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLtypeI : IsTypeI L) (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    ∃ frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L, frob.kernel_eq_MF ∧
      hyp.W1 ≤ frob.complement.map L.subtype := by
  obtain ⟨frob₀, hker₀⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hLmax hLtypeI
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

/-- **Peterfalvi (13.17)**: if `S` is type II, a maximal subgroup over `N_G(U)` is type-I
Frobenius, contains `U` in its kernel, and has the stated complement alternatives (order `p q`,
containing a conjugate `W₂^y`).  Assembled from the type-I existence (13.17.a/b,
`exists_typeI_maximal_overNormalizer_U`), a `W₁`-containing Frobenius decomposition
(`exists_typeIFrobeniusData_W1_le`), and the complement structure (13.17.c,
`typeI_overNormalizer_complement`). -/
theorem typeII_overNormalizer_frobenius [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) (hTTypeII : IsTypeII hyp.T) :
    ∃ data : TypeIOverNormalizerData hyp,
      data.frobenius.kernel_eq_MF ∧ (hyp.U ≤ data.H) := by
  obtain ⟨L, hLmax, hLtypeI, hNUL, hUH⟩ :=
    exists_typeI_maximal_overNormalizer_U _hG hyp hSTypeII hTTypeII
  obtain ⟨frob, hker, hW1E⟩ := exists_typeIFrobeniusData_W1_le _hG hyp hLmax hLtypeI hNUL
  obtain ⟨hcard, hy⟩ :=
    typeI_overNormalizer_complement _hG hyp hSTypeII hTTypeII hLmax hNUL hUH frob hW1E
  exact ⟨⟨L, maxNilpotentNormalHall L, hLmax, rfl, hNUL, frob, hUH, hcard, hy⟩, hker, hUH⟩

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
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLtypeI : IsTypeI L) (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    ∃ frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L, frob.kernel_eq_MF ∧
      hyp.W2 ≤ frob.complement.map L.subtype := by
  obtain ⟨frob₀, hker₀⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hLmax hLtypeI
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

/-- **Peterfalvi (13.17.c), V-side dual — faithful dichotomy form** (hub issue 3004, ruling 3):
for the `W₂`-containing Frobenius complement `E` of the type-I maximal `L` over `N_G(V)`, either
`E = W₂` (the `L = H ⋊ W₂` branch, `e = p`), or `E ⊓ P = W₂` and `E ⊄ P` (the
`L = H ⋊ (W₂W₁^y)` branch, leading to `e = pq`).  Unlike the S-side
(`complement_inf_Q_structure`, whose small branch is excluded by (14.5)), both branches are live
here; the resolution to `e = pq` happens only inside (14.11). -/
theorem complement_inf_P_structure_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW2E : hyp.W2 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype = hyp.W2 ∨
      (frob.complement.map L.subtype ⊓ hyp.P = hyp.W2 ∧
        ¬ frob.complement.map L.subtype ≤ hyp.P) := sorry

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
    (hyp : Hypothesis (G := G)) (hTII : IsTypeII hyp.T) :
    ∃ (M : Subgroup G) (_typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis M),
      M ∈ maximalSubgroups G ∧
        Subgroup.normalizer (hyp.V : Set G) ≤ M ∧
          (((maxNilpotentNormalHall M).subgroupOf M).index = hyp.p ∨
            ((maxNilpotentNormalHall M).subgroupOf M).index = hyp.p * hyp.q) := by
  obtain ⟨L, hLmax, hLtypeI, hNVL, _hVH⟩ :=
    exists_typeI_maximal_overNormalizer_V hG hyp hTII
  obtain ⟨frob, _hker, hW2E⟩ := exists_typeIFrobeniusData_W2_le hG hyp hLmax hLtypeI hNVL
  obtain ⟨typeIHyp⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis hG hLmax hLtypeI
  refine ⟨L, typeIHyp, hLmax, hNVL, ?_⟩
  rw [typeIFrobenius_kernel_index_eq_complement frob]
  exact complement_card_p_or_pq_V hG hyp frob hW2E

/-- Carrier for the virtual character `beta_j` and `Gamma_j` in Peterfalvi (13.18).

**De-opacified (W3 §15); faithful to Peterfalvi (13.18) after the issue-3003 correction.**  This
carrier previously held six free `_formula : Prop` placeholders (the
[[scaffold-sorry-free-not-done]] convention).  Since `BetaData` has no external consumers (only
`beta_support_norm_and_remainder` produces it), the fields are now the **genuine Peterfalvi (13.18)
statements** about `β_j`/`Γ`, tied to `hyp`, the grid `hyp.eta`, and `S`:

* `support_formula` — **(13.18.a)** the support of `β_j` is contained in `S`'s η-carrier support;
* `norm_formula` — **(13.18.b)** `‖β_j‖²_S = (u−1)/q + 2` (its Frobenius `Ind` half is the sorry-free
  `norm_induce_one_frobenius`);
* `Gamma_orthogonal_one` — **(13.18.c)** `(Γ, 1_G) = 0`, the residual is orthogonal to the principal;
* `Gamma_real` — **(13.18.c)** `Γ` is real (`Γ.conj = Γ`);
* `Y_norm_bound` — **(13.18.d)** for any split `Γ = X + Y` (`X ⊥ Y`, `Y ⊥` grid), `‖Y‖² ≤ (u−1)/q`.

The remaining half of **(13.18.c)** — `Γ`'s `j`-independence (`defGamma`) — is the standalone proven
`gammaGrid_defGamma` (not a field here, to keep the `FiniteInduce` `τ_S` instances out of this
structure's explicit inner-product binders).  ⚠ The **removed** fields `Gamma_independent`
(`⟨Γ,η_ik⟩ = 0`) and the old `Y_norm_bound` (`‖Γ‖² ≤ (u−1)/q + 1`) were **overstatements** — (13.18.c)
says `Γ` is independent of `j`, not grid-orthogonal, and (13.18.d) bounds the grid-orthogonal part
`Y`, not `‖Γ‖²` (issue 3003).

The genuine grid/Dade content bottoms out at the (3.2) τ-isometry (`tau3`, σ-pinned 2026-06-15) and
the (13.18.b) Frobenius norm; it is isolated into the single faithful producer
`betaData_of_grid`. -/
structure BetaData (hyp : Hypothesis (G := G)) where
  j : Fin hyp.p
  j_ne_zero : (j : ℕ) ≠ 0
  beta : ClassFunction ↥hyp.S ℂ
  Gamma : ClassFunction G ℂ
  /-- **(13.18.a)** support control: `β_j` is supported on `S`'s η-carrier support. -/
  support_formula : beta.support ⊆ ⋃ (i : Fin hyp.q), (hyp.mu i j).support
  /-- **(13.18.b)** norm: `‖β_j‖²_S = (u−1)/q + 2`, whose `Ind_{PW₁}^S 1` half is
  `norm_induce_one_frobenius`. -/
  norm_formula :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner beta beta
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)
  /-- **(13.18)** `Γ_j` is orthogonal to the principal character `1_G` (part of (13.18.c)). -/
  Gamma_orthogonal_one :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ClassFunction.inner Gamma (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0
  /-- **(13.18.c)** `Γ_j` is a real virtual character. -/
  Gamma_real : Gamma.conj = Gamma
  /-- **(13.18.d)** residual-norm bound: for any split `Γ = X + Y` with `X ⊥ Y` and `Y` orthogonal
  to the whole `η`-grid, `‖Y‖² ≤ (u−1)/q`.  This is the genuine (13.18.d) feeding the (14.14)
  case-`(c1)`/`(c2)` orthogonality switch.  (The previous field `‖Γ‖² ≤ (u−1)/q + 1` was **not**
  this statement — an overstatement, since `‖Γ‖² = ‖X‖² + ‖Y‖²` with `X` the nonzero grid-component;
  see issue 3003.  The (13.18.c) `j`-independence half is the standalone `gammaGrid_defGamma`.) -/
  Y_norm_bound :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (X Y : ClassFunction G ℂ), Gamma = X + Y → ClassFunction.inner X Y = 0 →
        (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
        (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ)

/-- **`U ⋊ W₁` complements `P` in `S`** (structural bridge for (13.18.b), `S`-side form).  From the
`Sdata` complements `M' ⋊ W₁ = S` and `P ⋊ U = M'`, the subgroup `U ⊔ W₁` intersects `P = S_F`
trivially and joins with it to `S`.  This is the `↥S`-internal `IsComplement'` behind the Frobenius
quotient `S̄ = S/P ≅ U ⋊ W₁` used to evaluate `‖Ind_{PW₁}^S 1‖²`.  (Re-derived here in the (13.18)
carve-out rather than exposed from `coprime_card_P_card_UW1`, whose derivation it mirrors.) -/
theorem uW1_isComplement_P [Finite G] (hyp : Hypothesis (G := G)) :
    Subgroup.IsComplement' ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) (hyp.P.subgroupOf hyp.S) := by
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hU_le_M' : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hUW1_le_S : hyp.U ⊔ hyp.W1 ≤ hyp.S := sup_le (hU_le_M'.trans hM'_le_S) hW1_le_S
  have hdisj : hyp.P ⊓ hyp.U = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.derived_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxH, hxU⟩
    have hxD : x ∈ derivedInG hyp.S := hyp.Sdata.H_le (by rwa [hyp.Sdata.H_eq, ← hyp.P_eq_SF])
    have hmem : (⟨x, hxD⟩ : ↥(derivedInG hyp.S)) ∈
        (hyp.Sdata.H.subgroupOf (derivedInG hyp.S)) ⊓ (hyp.Sdata.U.subgroupOf (derivedInG hyp.S)) :=
      ⟨Subgroup.mem_subgroupOf.mpr (by rwa [hyp.Sdata.H_eq, ← hyp.P_eq_SF]),
        Subgroup.mem_subgroupOf.mpr (hyp.Sdata_U_eq ▸ hxU)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  have hM'W1 : derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW1⟩
    have hxS : x ∈ hyp.S := hM'_le_S hxM'
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((derivedInG hyp.S).subgroupOf hyp.S) ⊓ (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  have hSsup : hyp.P ⊔ (hyp.U ⊔ hyp.W1) = hyp.S := by
    have htop := hyp.Sdata.M_complement.sup_eq_top
    have hmap := congrArg (Subgroup.map hyp.S.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM'_le_S,
      Subgroup.map_subgroupOf_eq_of_le hyp.Sdata.W1_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [hyp.Sdata_W1_eq, hyp.S_deriv_eq_PU] at hmap
    rw [← sup_assoc]; exact hmap
  have hPUW1_disj : hyp.P ⊓ (hyp.U ⊔ hyp.W1) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxP, hxUW1⟩ := Subgroup.mem_inf.mp hx
    have hxUW1' : (x : G) ∈ (↑(hyp.U ⊔ hyp.W1) : Set G) := hxUW1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.U hyp.W1 hyp.W1_normalizes_U] at hxUW1'
    obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_mul.mp hxUW1'
    have hwM' : w ∈ derivedInG hyp.S := by
      have : w = u⁻¹ * x := by rw [← huw]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hU_le_M' (SetLike.mem_coe.mp hu)))
        (hP_le_M' hxP)
    have hw1 : w = 1 := by
      have : w ∈ derivedInG hyp.S ⊓ hyp.W1 := Subgroup.mem_inf.mpr ⟨hwM', SetLike.mem_coe.mp hw⟩
      rwa [hM'W1, Subgroup.mem_bot] at this
    have hxu : x = u := by rw [← huw, hw1, mul_one]
    have hxPU : x ∈ hyp.P ⊓ hyp.U := Subgroup.mem_inf.mpr ⟨hxP, hxu ▸ SetLike.mem_coe.mp hu⟩
    rwa [hdisj, Subgroup.mem_bot] at hxPU
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff, eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hy
    have hyPU : (y : G) ∈ hyp.P ⊓ (hyp.U ⊔ hyp.W1) := ⟨hy.2, hy.1⟩
    rw [hPUW1_disj, Subgroup.mem_bot] at hyPU
    rw [Subgroup.mem_bot]; exact Subtype.ext hyPU
  · have hsup : ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊔ (hyp.P.subgroupOf hyp.S) = ⊤ := by
      rw [sup_comm, ← Subgroup.subgroupOf_sup hP_le_S hUW1_le_S, hSsup, Subgroup.subgroupOf_self]
    rw [← Subgroup.mul_normal, hsup, Subgroup.coe_top]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The induced trivial character** `Ind_{P⋊W₁}^S(1)` of the subgroup `P ⋊ W₁ ≤ S`, the
positive part of the (13.18) bridge character `β_j`.  Its squared `S`-norm is the Frobenius
value `(u−1)/q + 1` (`norm_induce_one_frobenius` composed with the `S̄ = S/P = U⋊W₁` inflation). -/
noncomputable def indPW1 [Finite G] (hyp : Hypothesis (G := G)) : ClassFunction ↥hyp.S ℂ :=
  ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
    (trivialClassFunction ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S))

/-- **Peterfalvi (13.18) `S`-side virtual character** `β_j := Ind_{P⋊W₁}^S(1) − μ_{0j}`
(Coq `PFsection13.FTtypeP_bridge`).  The induced trivial character `indPW1 hyp` of `P ⋊ W₁ ≤ S`
minus the base-row grid irreducible `μ_{0j} = hyp.mu 0 j`. -/
noncomputable def betaGrid [Finite G] (hyp : Hypothesis (G := G)) (j : Fin hyp.p) :
    ClassFunction ↥hyp.S ℂ :=
  indPW1 hyp - hyp.mu ⟨0, hyp.q_prime.pos⟩ j

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The genuine `S`-side Dade image** `τ_S(β_{#1})` of the (13.18) bridge character at column
`#1`.  Uses the honest (13.2.e) Dade isometry `τ_S = dadeIntegralCharacterMap (hyp.dadeHypS0 hG) …`
— the `S`-instance of the (5.3) Dade map — **NOT** the off-path `= 0` placeholder `hyp.tauS`. -/
noncomputable def tauSbetaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ClassFunction G ℂ :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
    (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18) residual** `Γ := τ_S(β_{#1}) − 1_G + η_{01}` (Coq
`PFsection13.FTtypeP_bridge_gap`).  `η_{01} = hyp.eta 0 1` is the (3.3) grid image `τ₃(ω_{01})`;
`1_G = constOne G`.  Note `Γ` does not depend on the column `j` of `βData`. -/
noncomputable def GammaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ClassFunction G ℂ :=
  tauSbetaGrid hG hyp - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
    + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩

/-- **(13.18.a) support control** (`S`-side, grid form): `supp(β_j) ⊆ ⋃_i supp(μ_{ij})`.

⚠ DEEP §13 RESIDUAL, isolated obligation.  This is Coq's `PVSbeta`/`A0beta` (`β_j ∈ CF(S, P^# ∪
V_S) ⊆ CF(S, A₀(S))`), restated here in the grid-support form the (13.19)/(14.9) consumers use:
off `⋃_i supp(μ_{ij})` the induced permutation character `Ind_{PW₁}^S 1` exactly cancels `μ_{0j}`.
The cancellation is the `normedTI` structure of the `W₁`-classes in `S̄ = S/P` (Coq `gammaW1`,
`Ptype_Fcore_sdprod`); no repo API yet supplies it. -/
theorem betaGrid_support [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    (betaGrid hyp j).support ⊆ ⋃ (i : Fin hyp.q), (hyp.mu i j).support := sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.b), Frobenius half** (`FiniteInduce`-instance form): `‖Ind_{PW₁}^S 1‖²_S = (u−1)/q + 1`.
The wrapper `indPW1_inner_self` bridges to arbitrary `Fintype`/`Invertible` instances. -/
private theorem indPW1_inner_self_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
      ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := by
  classical
  -- Structural setup: `U ⋊ W₁` complements `P` in `S`.
  have hcompl := uW1_isComplement_P hyp
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hU_le_M' : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hUW1_le_S : hyp.U ⊔ hyp.W1 ≤ hyp.S := sup_le (hU_le_M'.trans hM'_le_S) hW1_le_S
  have hW1_le_UW1 : hyp.W1 ≤ hyp.U ⊔ hyp.W1 := le_sup_right
  have hW1_le_PW1 : hyp.W1 ≤ hyp.P ⊔ hyp.W1 := le_sup_right
  have hP_le_PW1 : hyp.P ≤ hyp.P ⊔ hyp.W1 := le_sup_left
  have hPW1_le_S : hyp.P ⊔ hyp.W1 ≤ hyp.S := sup_le hP_le_S hW1_le_S
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono hP_le_PW1
  -- Step 1: `indPW1 = (Ind_{Ā}^{S̄} 1) ∘ mk'`, so its `S`-norm equals the `S̄`-norm (P2 + P1).
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA,
    OddOrder.RepresentationTheory.inner_compHom_mk'_eq]
  -- Step 2: `S̄ = S/P` is Frobenius via the iso `e : ↥(U⊔W₁) ≃* S̄`.
  -- The `U ⋊ W₁` Frobenius, read off `Sdata` sorry-free (`typeP_uW1_frobenius`), avoiding the
  -- §16-gated `basic_structure` so this stays honestly sorry-free.
  have hSdataUne : hyp.Sdata.U ≠ ⊥ := (hyp.toTypesIIIIIIVSetupS _hG).nontrivial.1
  have hUW1frob : Ch06.IsFrobeniusGroup ↥(hyp.U ⊔ hyp.W1)
      (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1)) (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)) := by
    have h := S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    rw [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at h
    exact h
  set f : ↥(hyp.U ⊔ hyp.W1) →* (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) :=
    (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)).comp (Subgroup.inclusion hUW1_le_S) with hf
  have he_apply : ∀ w : ↥(hyp.U ⊔ hyp.W1),
      f w = QuotientGroup.mk (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S) := by
    intro w
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rw [he_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hw
    have hwUW1S : (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S) ∈ (hyp.U ⊔ hyp.W1).subgroupOf hyp.S := by
      rw [Subgroup.mem_subgroupOf]; exact w.2
    have hbot : (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S)
        ∈ ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊓ (hyp.P.subgroupOf hyp.S) :=
      Subgroup.mem_inf.mpr ⟨hwUW1S, Subgroup.mem_subgroupOf.mpr hw⟩
    rw [disjoint_iff.mp hcompl.disjoint, Subgroup.mem_bot] at hbot
    exact Subtype.ext (by simpa using congrArg Subtype.val hbot)
  have hcard : Fintype.card ↥(hyp.U ⊔ hyp.W1)
      = Fintype.card (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      show Nat.card (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) = (hyp.P.subgroupOf hyp.S).index from rfl,
      hcompl.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW1_le_S).toEquiv]
  set e : ↥(hyp.U ⊔ hyp.W1) ≃* (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) :=
    MulEquiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩) with he
  have he_toMonoidHom : ∀ w, e.toMonoidHom w = f w := fun _ => rfl
  -- Transport the `U ⋊ W₁` Frobenius structure to `S̄`.
  have hFrob := Ch06.isFrobeniusGroup_map_equiv hUW1frob e
  -- The transported complement `W̄₁.map e` equals the (13.18) induction subgroup `Ā = (PW₁)/P`.
  have hAmatch : (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)).map e.toMonoidHom
      = ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
          (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)) := by
    apply le_antisymm
    · rintro _ ⟨w, hwW1, rfl⟩
      have hwW1' : (w : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hwW1)
      refine Subgroup.mem_map.mpr ⟨⟨(w : G), hPW1_le_S (hW1_le_PW1 hwW1')⟩,
        Subgroup.mem_subgroupOf.mpr (hW1_le_PW1 hwW1'), ?_⟩
      rw [QuotientGroup.mk'_apply, he_toMonoidHom, he_apply]
    · rintro _ ⟨s, hsPW1, rfl⟩
      have hsG : (s : G) ∈ hyp.P ⊔ hyp.W1 :=
        Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hsPW1)
      have hsmem : (s : G) ∈ (↑(hyp.P ⊔ hyp.W1) : Set G) := hsG
      rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.P hyp.W1 (hW1_le_S.trans hS_norm_P)]
        at hsmem
      obtain ⟨p, hp, w, hw, hpw⟩ := Set.mem_mul.mp hsmem
      have hwW1 : w ∈ hyp.W1 := SetLike.mem_coe.mp hw
      have hpP : p ∈ hyp.P := SetLike.mem_coe.mp hp
      refine Subgroup.mem_map.mpr ⟨⟨w, hW1_le_UW1 hwW1⟩,
        Subgroup.mem_subgroupOf.mpr hwW1, ?_⟩
      have hs_eq : s = (⟨p, hP_le_S hpP⟩ : ↥hyp.S) * ⟨w, hW1_le_S hwW1⟩ :=
        Subtype.ext (by rw [Subgroup.coe_mul]; exact hpw.symm)
      have hp1 : QuotientGroup.mk' (hyp.P.subgroupOf hyp.S) ⟨p, hP_le_S hpP⟩ = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact Subgroup.mem_subgroupOf.mpr hpP
      rw [he_toMonoidHom, he_apply, ← QuotientGroup.mk'_apply, hs_eq, map_mul, hp1, one_mul]
  rw [hAmatch] at hFrob
  -- Frobenius norm on `S̄`.
  rw [norm_induce_one_frobenius hFrob]
  -- `|Ā| = |W₁| = q`.
  have hcardAmap : Nat.card ↥(((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
      (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S))) = hyp.q := by
    rw [← hAmatch,
      Nat.card_congr (Subgroup.equivMapOfInjective (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1))
        e.toMonoidHom e.injective).symm.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1_le_UW1).toEquiv, ← hyp.q_eq_card_W1]
  -- `Ā.index = |Ū| = |U| = u` (using `c = 1`, Pf (13.12)).
  have hindexAmap : (((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
      (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S))).index = hyp.u := by
    rw [hFrob.isComplement.index_eq_card,
      Nat.card_congr (Subgroup.equivMapOfInjective (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1))
        e.toMonoidHom e.injective).symm.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : hyp.U ≤ _)).toEquiv,
      hyp.card_U_eq_uc, c_eq_one _hG hyp, mul_one]
  rw [invOf_eq_inv, hcardAmap, hindexAmap]
  have hq : (hyp.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne'
  push_cast
  field_simp
  ring

/-- **(13.18.b), Frobenius half**: `‖Ind_{PW₁}^S 1‖²_S = (u−1)/q + 1`.

By the inflation `Ind_{PW₁}^S 1 = Ind_{W̄₁}^{S̄} 1` inflated through `P` (P2
`induce_one_eq_compHom_induce_one_of_le` + P1 `inner_compHom_mk'_eq`), its `S`-norm equals
`‖Ind_{W̄₁}^{S̄} 1‖²` in the Frobenius quotient `S̄ = S/P ≅ U⋊W₁` (`uW1_isComplement_P` transported
by `isFrobeniusGroup_map_equiv`), which `norm_induce_one_frobenius` evaluates to
`(|U|−1)/|W₁| + 1 = (u−1)/q + 1` (using `c = 1`, Pf (13.12), so `|U| = u`).  The
`FiniteInduce`-instance content is `indPW1_inner_self_aux`; here we bridge to the caller's
`Fintype`/`Invertible` instances (both `Subsingleton`). -/
theorem indPW1_inner_self [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := by
  intro _ _
  convert indPW1_inner_self_aux _hG hyp using 2
  exact Subsingleton.elim _ _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`P ⊄ ker μ_{0j}`** (Pf (13.18.b) kernel step, `S`-side).  For `j ≠ 0`, the base-row grid
irreducible `μ_{0j}` does not have the Fitting kernel `P` in its character kernel.

Contrapositive of Peterfalvi's argument (mirroring `PrimeTIResidue.constituent_P_not_subset_ker`):
if `P ⊆ ker μ_{0j}` then `W₂ ⊆ P ⊆ ker μ_{0j}`, so `Res_{S'} μ_{0j}` is trivial on the `W₂`-part
(`characterKernel_restrict_subgroupOf`); its constituent `ψ` — the (4.5.a) source of
`μ_j = ∑_i μ_{ij} = Ind_{S'} ψ`, with `⟨Res_{S'} μ_{0j}, ψ⟩ = 1` by Frobenius reciprocity — inherits
that kernel containment (`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), contradicting the
`mu_colSum_eq_induce` clause `W₂ ⊄ ker ψ`. -/
theorem P_not_subset_characterKernel_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)) := by
  classical
  set μ0 := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμ0
  have hW2_le_P : hyp.W2 ≤ hyp.P := by
    have h := hyp.Sdata.W2_le
    rw [hyp.Sdata_W2_eq, hyp.Sdata.H_eq, ← hyp.P_eq_SF] at h
    exact h.trans inf_le_left
  intro hPker
  obtain ⟨psiS, hpsiIrr, hpsiInd, hpsiW2⟩ := hyp.mu_colSum_eq_induce j
  have hj' : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by rw [h])
  have hW2notpsi := hpsiW2 hj'
  have hW2Sker : (hyp.W2.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel μ0 :=
    fun x hx => hPker (Subgroup.comap_mono hW2_le_P hx)
  have hRker := OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf
    ((derivedInG hyp.S).subgroupOf hyp.S) hW2Sker
  have hResChar := OddOrder.Peterfalvi.S08.isCharacter_restrict
    (hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j).isCharacter
    ((derivedInG hyp.S).subgroupOf hyp.S)
  -- `⟨∑_i μ_{ij}, μ_{0j}⟩ = 1` (orthonormality: only the `i = 0` term survives).
  have hmul : ClassFunction.inner (∑ i, hyp.mu i j) μ0 = 1 := by
    rw [inner_sum_left]
    refine (Finset.sum_eq_single ⟨0, hyp.q_prime.pos⟩ (fun i _ hi => ?_)
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨hyp.mu i j, hyp.mu_irreducible i j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      rw [if_neg (fun heq => hi (hyp.mu_col_injective j
        (congrArg (fun χ : IrreducibleCharacter ↥hyp.S => (χ : ClassFunction ↥hyp.S ℂ)) heq)))] at h
      exact h
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      simpa using h
  have hfrob := ClassFunction.inner_induce_eq_inner_restrict
    ((derivedInG hyp.S).subgroupOf hyp.S) psiS μ0
  rw [← hpsiInd, hmul] at hfrob
  have hinner : ClassFunction.inner
      (ClassFunction.restrict ((derivedInG hyp.S).subgroupOf hyp.S) μ0) psiS ≠ 0 := by
    rw [RepresentationTheory.inner_conj_symm, ← hfrob]; simp
  exact hW2notpsi (fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hpsiIrr hinner (hRker hx))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.b) orthogonality half** (`FiniteInduce`-instance form). -/
private theorem indPW1_inner_mu_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  classical
  have hP_le_S : hyp.P ≤ hyp.S :=
    (by rw [hyp.S_deriv_eq_PU]; exact le_sup_left : hyp.P ≤ derivedInG hyp.S).trans
      (Subgroup.map_subtype_le _)
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  haveI hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono le_sup_left
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA]
  exact OddOrder.RepresentationTheory.inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker _
    ⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ j, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
    (P_not_subset_characterKernel_mu _hG hyp j hj)

/-- **(13.18.b), orthogonality half**: `⟨Ind_{PW₁}^S 1, μ_{0j}⟩ = 0` for `j ≠ 0`.

`Ind_{PW₁}^S 1 = (Ind_{Ā}^{S̄} 1) ∘ mk'` (P2) is inflated from `S̄ = S/P`, so all its irreducible
constituents kill `P`; `μ_{0j}` does not (`P_not_subset_characterKernel_mu`), so they are orthogonal
(`inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker`).  `_aux` carries the `FiniteInduce`
instances; the wrapper bridges to the caller's (`Subsingleton`). -/
theorem indPW1_inner_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  intro _ _
  convert indPW1_inner_mu_aux _hG hyp j _hj using 2
  exact Subsingleton.elim _ _

/-- **(13.18.b) norm**: `‖β_j‖²_S = (u−1)/q + 2`.

Genuine reduction: `β_j = Ind_{PW₁}^S 1 − μ_{0j}`, so by bilinearity
`‖β_j‖² = ‖Ind‖² − ⟨Ind,μ_{0j}⟩ − ⟨μ_{0j},Ind⟩ + ‖μ_{0j}‖²`.  Here `‖μ_{0j}‖² = 1` is **proven**
from `hyp.mu_irreducible` (via `irreducibleCharacter_inner_eq_ite`), `⟨μ_{0j},Ind⟩ = 0` follows
from `⟨Ind,μ_{0j}⟩ = 0` by conjugate symmetry, and the remaining `‖Ind‖² = (u−1)/q + 1`
(`indPW1_inner_self`) and `⟨Ind,μ_{0j}⟩ = 0` (`indPW1_inner_mu`) are the isolated §13 obligations.
`(u−1)/q + 1 + 1 = (u−1)/q + 2`. -/
theorem betaGrid_norm [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (betaGrid hyp j) (betaGrid hyp j)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ) := by
  intro _ _
  set μ := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμdef
  have hμμ : ClassFunction.inner μ μ = 1 := by
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩)
    simpa using hite
  have hIμ : ClassFunction.inner (indPW1 hyp) μ = 0 := indPW1_inner_mu hG hyp j hj
  have hμI : ClassFunction.inner μ (indPW1 hyp) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hIμ, star_zero]
  have hII : ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := indPW1_inner_self hG hyp
  have hbeta : betaGrid hyp j = indPW1 hyp - μ := rfl
  rw [hbeta, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hII, hIμ, hμI, hμμ]
  push_cast
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.8)/(5.3) prime-`TI` Dade cross-relation, `S`-side row-`0` form**:
`τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` for `j ≠ 0`.

This is Coq `prDade_sub_TIirr` (`PFsection4.v:870`) `τ(μ2_{ij} − μ2_{ik}) = δ_j·(η_{ij} − η_{ik})`
specialized to row `i = 0`, columns `j` and `#1`, with the `FT`-context sign `δ_j = 1`.  It is the
single deep input behind (13.18.c)'s `j`-independence `gammaGrid_defGamma`.

✅ **Now on the correct Dade map** (issue 9076, 2026-07-08): `τ_S` is `dadeIntegralCharacterMap`
of the honest **`'A0(S)`-Dade** `dadeHypS0` (support `A₀(S) = A(S) ∪ V^S`), **not** the smaller
`'A(S)`-Dade `dadeHypS`.  The `μ`-column difference `μ_{0j} − μ_{01}` is supported on `P^# ∪ V_S`
(Coq `prDade_sub_TIirr_on`), and `V_S ⊄ S' ⊇ A(S)`, so with the old `dadeHypS` map the `V_S`-part
fell in the arbitrary linear-extension region and the statement was **unprovable as stated**; the
`'A0`-Dade correction fixes that (`dadeHypS0` inherits one deep FT-support pin,
`not_isConj_honestTypeP2ASet_typePV`).

Remaining to discharge the `sorry` (rigidity engine now available): `X := τ_S(μ-diff)` has
`‖X‖² = 2` (Dade isometry) and `X ∈ ZIrr`; it agrees with `η_{0j} − η_{01}` on the regular set via
`τ_S = Ind_S^G` on `A₀`-supported (`normedTI 'A0`, `H = ⊥`) + the prime-`TI` `μ`-value
`μ_{0j}|_V = ω`-value (Coq `prTIirr_id`, prime-`TI` theory — not yet ported, cf. 9014); then
`X = η_{0j} − η_{01}` by `S16.eta_diff_rigidity` (Peterfalvi (3.8), issue 9076 piece 4b). -/
theorem tauS_mu_row0_cross [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ j
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
  classical
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) with hD
  by_cases hj1 : j = ⟨1, by have := hyp.three_le_p; omega⟩
  · -- Trivial column `j = #1`: both `μ`- and `η`-differences vanish, and `τ_S 0 = 0`.
    simp only [hj1, sub_self, map_zero]
  · -- `j ≠ #1`: `X := τ_S(μ_{0j} − μ_{0,#1})` is a norm-`2` `ZIrr` character agreeing with
    -- `η_{0j} − η_{0,#1}` on the regular set `V`, so `S16.eta_diff_rigidity` (3.8) pins it.
    have hμaIrr : IsIrreducibleCharacter (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) :=
      hyp.mu_irreducible _ _
    have hμbIrr : IsIrreducibleCharacter
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) :=
      hyp.mu_irreducible _ _
    have hμne : hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ :=
      hyp.mu_row0_ne hj1
    have hsupp := hyp.tauS_mu_row0_diff_support j
    have hZIrrS : (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        ∈ ZIrr (↥hyp.S) :=
      (ZIrr (↥hyp.S)).sub_mem hμaIrr.mem_ZIrr hμbIrr.mem_ZIrr
    -- (a) `X ∈ ZIrr G` (Dade sends supported virtual characters to virtual characters, `(2.6.b)`).
    have hXZ : D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) ∈ ZIrr G :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypS0 hG) (hyp.dadeHypS0_hconj hG) hsupp hZIrrS
    -- (b) `‖μ_{0j} − μ_{0,#1}‖² = 2` (two distinct irreducibles).
    have hinner : ∀ φ ψ : ClassFunction ↥hyp.S ℂ, IsIrreducibleCharacter φ →
        IsIrreducibleCharacter ψ → ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥hyp.S)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥hyp.S)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have h_ab : ClassFunction.inner (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 := by
      rw [hinner _ _ hμaIrr hμbIrr, if_neg hμne]
    have h_ba : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [hinner _ _ hμbIrr hμaIrr, if_neg (Ne.symm hμne)]
    have hnorm2 : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 2 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h_ab, h_ba,
        hμaIrr.inner_self_eq_one, hμbIrr.inner_self_eq_one]
      ring
    have hX2 : ClassFunction.inner
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩))
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) = 2 := by
      rw [hD, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS0 hG) (hyp.dadeHypS0_hconj hG) hsupp hsupp]
      exact hnorm2
    -- (c) `X − (η_{0j} − η_{0,#1})` vanishes on the regular set `V` (prime-`TI` `V`-value pin).
    have hvanish : ∀ x ∈ conjClassSet
          ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
              - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
          - ((1 : ℤ) : ℂ) • (hyp.eta ⟨0, hyp.q_prime.pos⟩ j
              - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) x = 0 := by
      intro x hx
      have hv := hyp.tauS_mu_row0_vanish_on_V hG j x hx
      simpa [hD] using hv
    -- (3.8) rigidity: a norm-`2` `ZIrr` character agreeing with `η_{0j} − η_{0,#1}` on `V` is it.
    have hrig := OddOrder.Peterfalvi.S16.eta_diff_rigidity hyp hXZ hX2
      ⟨0, hyp.q_prime.pos⟩ hj1 (s := (1 : ℤ)) (Or.inl rfl) hvanish
    rw [Int.cast_one, one_smul] at hrig
    exact hrig

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c), `j`-independence** (`defGamma`): for every column `j ≠ 0`, the bridge residual
`τ_S(β_j) − 1_G + η_{0j}` equals the fixed gap `Γ = GammaGrid` (defined at column `#1`).

This is exactly Peterfalvi (13.18.c)'s "`Γ` is independent of `j`" (Coq `defGamma`,
`PFsection13.v:1905`), **NOT** grid-orthogonality: the previous scaffold field
`Gamma_independent : ⟨Γ, η_{ik}⟩ = 0` was an **overstatement** (issue 3003), refuted by the genuine
(13.18.d) `X + Y` decomposition where `Γ`'s grid-component `X` is nonzero.

Proof (sorry-free glue, one isolated obligation): `τ_S(β_j) − τ_S(β_{#1}) = τ_S(β_j − β_{#1})` by
`ℤ`-linearity of the Dade map (`map_sub`), and `β_j − β_{#1} = μ_{01} − μ_{0j} = −(μ_{0j} − μ_{01})`
(both share the `Ind_{PW₁}^S 1` positive part), so `τ_S(β_j − β_{#1}) = −(η_{0j} − η_{01}) =
η_{01} − η_{0j}` by the (4.8)/(5.3) cross-relation `tauS_mu_row0_cross`.  Cancelling the `−1_G`'s and
`abel` closes the goal. -/
theorem gammaGrid_defGamma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) (betaGrid hyp j)
        - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + hyp.eta ⟨0, hyp.q_prime.pos⟩ j
      = GammaGrid hG hyp := by
  have hcross := tauS_mu_row0_cross hG hyp j hj
  have hbeta : betaGrid hyp j - betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩
      = -(hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) := by
    simp only [betaGrid]; abel
  have key : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) (betaGrid hyp j)
      - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG))
          (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
        - hyp.eta ⟨0, hyp.q_prime.pos⟩ j := by
    rw [← map_sub, hbeta, map_neg, hcross]; abel
  simp only [GammaGrid, tauSbetaGrid]
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData (hyp.dadeHypS0_hconj hG)) with hD
  rw [← sub_eq_zero, show
      (D (betaGrid hyp j) - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        - (D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
          - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = (D (betaGrid hyp j) - D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩))
        - (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) by abel, key, sub_self]

/-- **The Coq `A0beta` inclusion `P^# ∪ V_S ⊆ 'A0(S)`** (the final step of (13.18.a)): the sharp
Fitting kernel `P^#` and the `S`-class-closure of the cyclic-TI set `V = W − (W₁ ∪ W₂)` both land
in the honest `A₀(S) = A(S) ∪ V^S`.  The `V^S` part is the definitional right component (after the
`Sdata.W1/W2` synchronization); `P^#` lands in `A(S) = centralizerSupport (S_σ^#) S'` because
`P = S_F = S_σ` (type `P₂`, `maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`), `P ≤ S' = P ⊔ U`,
and every element self-centralizes. -/
theorem sharpP_union_V_subset_A0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    sharpSubgroup hyp.P ∪
        conjClassSetIn hyp.S (typePV hyp.S hyp.Sdata)
      ⊆ honestTypeP2A0Set hyp.S hyp.Sdata := by
  have hPeq : hyp.P = OddOrder.BG.Ch3.S10.Msigma hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG
      hyp.S_maximal
      (Or.inr (OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.S_maximal hyp.S_typeP2))
  intro z hz
  rcases hz with hzP | hzV
  · -- `P^# ⊆ A(S) ⊆ A₀(S)`.
    refine honestTypeP2ASet_subset_A0Set hyp.Sdata ?_
    obtain ⟨hzP_mem, hz1⟩ := hzP
    rw [Set.mem_singleton_iff] at hz1
    refine mem_honestTypeP2ASet.mpr ⟨?_, hz1, z, ⟨hPeq ▸ hzP_mem, ?_⟩, ?_⟩
    · have hPle : hyp.P ≤ derivedInG hyp.S := by
        rw [hyp.S_deriv_eq_PU]; exact le_sup_left
      exact hPle hzP_mem
    · rwa [Set.mem_singleton_iff]
    · exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
        rw [Set.mem_singleton_iff] at hw; subst hw; rfl
  · exact Set.mem_union_right _ hzV

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.a), `'A0(S)`-support form**: `supp(β_j) ⊆ 'A0(S)` for `j ≠ 0`.

The Coq `A0beta` (`PFsection13.v:1870`), obtained from `PVSbeta` (`β_j ∈ 'CF(S, P^# ∪ V_S)`,
`PFsection13.v:1833`) via `P^# ∪ V_S ⊆ 'A0(S)`.  `PVSbeta` cancels the induced permutation character
`Ind_{PW₁}^S 1` against `μ_{0j}` off `P^# ∪ V_S`, using the `W₁`-class `normedTI` structure in
`S̄ = S/P = Ū ⋊ W̄₁` (Coq `gammaW1`) together with the prime-`TI` residue value `prTIirr_id`; both
bottom out at the shared prime-`TI` residue content (issue 9014) that connects the free `μ`-grid to
the σ-residue theory.  **This single `'A0`-support obligation is what both `gammaGrid_orthogonal_one`
and `gammaGrid_Y_norm_bound` reduce to** (the honest `'A0`-Dade=Ind bridge
`sInstance_dade0_eq_induce`, issue 9076, then discharges the remaining Dade content). -/
theorem betaGrid_A0_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    (betaGrid hyp j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (honestTypeP2A0Set hyp.S hyp.Sdata) hyp.S := sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0`.

**De-scaffolded** (issue 9076): the `'A0(S)` `normedTI` content the old docstring flagged as
"missing" is now supplied by the honest `'A0`-Dade=Ind bridge `sInstance_dade0_eq_induce`.  Reduction
(Coq `oGamma1`): `⟨Γ,1⟩ = ⟨τ_S β_{#1},1⟩ − ⟨1,1⟩ + ⟨η_{01},1⟩`, and
* `⟨1,1⟩ = 1` (`constOne_inner_self_eq_one`);
* `⟨η_{01},1⟩ = 0` — grid orthogonality: `1_G = η_{00}` (`eta_principal_eq_trivial`) and `η_{01} ⊥
  η_{00}` (`eta_orthonormal`);
* `⟨τ_S β_{#1},1_G⟩ = 1` — the bridge gives `τ_S β_{#1} = Ind_S^G β_{#1}` (needs `β_{#1}` supported in
  `'A0(S)`, `betaGrid_A0_support`), so by Frobenius reciprocity (`inner_induce_eq_inner_restrict`)
  `⟨Ind_S^G β_{#1}, 1_G⟩ = ⟨β_{#1}, 1_S⟩ = ⟨Ind_{PW₁}^S 1, 1_S⟩ − ⟨μ_{01}, 1_S⟩ = 1 − 0`, where
  `⟨Ind 1, 1_S⟩ = 1` (`inner_induce_trivialChar_constOne_eq_one`) and `⟨μ_{01}, 1_S⟩ = 0` (`μ_{01}`
  irreducible and `≠ 1_S`, since `⟨Ind 1, μ_{01}⟩ = 0 ≠ 1`, `indPW1_inner_mu`).

The **single** remaining gate is `betaGrid_A0_support` (the (13.18.a) `'A0`-support). -/
private theorem gammaGrid_orthogonal_one_aux [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
  classical
  letI : Fintype ↥hyp.S := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `⟨Ind_{PW₁}^S 1, 1_S⟩ = 1`.
  have hind : ClassFunction.inner (indPW1 hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S)) = 1 := by
    rw [indPW1, ← OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
    exact OddOrder.Peterfalvi.S09.Cert.inner_induce_trivialChar_constOne_eq_one
      ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
  -- `⟨μ_{01}, 1_S⟩ = 0`: `μ_{01}` is irreducible and `≠ 1_S` (else `⟨Ind 1, μ_{01}⟩ = 1 ≠ 0`).
  have hmu : ClassFunction.inner
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S)) = 0 := by
    have hIμ : ClassFunction.inner (indPW1 hyp)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 :=
      indPW1_inner_mu hG hyp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)
    have hne : (⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩,
          hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩⟩ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
        ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥hyp.S := by
      intro heq
      apply one_ne_zero (α := ℂ)
      have hcf : hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          = OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S) :=
        congrArg (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S =>
          (χ : ClassFunction ↥hyp.S ℂ)) heq
      rw [hcf, hind] at hIμ
      exact hIμ
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩,
        hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥hyp.S)
    rw [if_neg hne] at hite
    exact hite
  -- `⟨τ_S(β_{#1}), 1_G⟩ = 1` via the `'A0`-Dade=Ind bridge + Frobenius reciprocity.
  have htau : ClassFunction.inner (tauSbetaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 1 := by
    have hbridge : tauSbetaGrid hG hyp
        = ClassFunction.induce hyp.S (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩) := by
      rw [tauSbetaGrid]
      exact hyp.sInstance_dade0_eq_induce hG
        (betaGrid_A0_support hG hyp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num))
    rw [hbridge, ClassFunction.inner_induce_eq_inner_restrict]
    have hres : ClassFunction.restrict hyp.S
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S) := by
      ext x; rw [ClassFunction.restrict_apply]; rfl
    rw [hres]
    simp only [betaGrid]
    rw [ClassFunction.inner_sub_left, hind, hmu, sub_zero]
  -- `⟨η_{01}, 1_G⟩ = 0`.
  have heta : ClassFunction.inner
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    have h00 : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ := by
      rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl
    rw [h00]
    have horth := OddOrder.Peterfalvi.S16.eta_orthonormal hyp
      ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.q_prime.pos⟩
      ⟨1, by have := hyp.three_le_p; omega⟩ ⟨0, hyp.p_prime.pos⟩
    rw [if_neg (by rintro ⟨-, h2⟩; exact absurd (congrArg Fin.val h2) (by norm_num))] at horth
    exact horth
  rw [GammaGrid, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one, htau, heta]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0` (public form).  Thin wrapper over `gammaGrid_orthogonal_one_aux`
that reconciles the caller's `Fintype G`/`Invertible (Nat.card G : ℂ)` instances with the
`FiniteInduce`-scoped ones the core proof uses (both are `Subsingleton`). -/
theorem gammaGrid_orthogonal_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ClassFunction.inner (GammaGrid hG hyp)
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
  intro _ _
  convert gammaGrid_orthogonal_one_aux hG hyp using 2 <;> exact Subsingleton.elim _ _

/-- **(13.18.c)** `Γ` is real: `Γ.conj = Γ`.

⚠ DEEP §13 RESIDUAL, isolated obligation.  Coq `GammaReal`: conjugation commutes with `Ind` and
with the Dade map (`cfAutInd`, `Dtau`), and sends grid entries to their conjugate index
(`prTIirr_aut`, `cfAut_cycTIiso`: `η̄_{0j} = η_{0,-j}`, `μ̄_{0j} = μ_{0,-j}`), so
`Γ̄ = τ_S(β̄_{#1}) − 1_G + η̄_{01}` collapses back to `Γ` via `defGamma` at the conjugate column.
The Dade/grid conjugation-commutation facts are not yet in the repo. -/
theorem gammaGrid_real [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (GammaGrid hG hyp).conj = GammaGrid hG hyp := sorry

/-- **(13.18.d) residual-norm bound**: for any split `Γ = X + Y` with `X ⊥ Y` and `Y` orthogonal to
the whole `η`-grid `{η_{ik}}`, `‖Y‖² ≤ (u−1)/q`.

⚠ DEEP §13 RESIDUAL, isolated obligation.  Coq's (13.18.d) argument (`PFsection13.v:1915-1934`)
bounds `‖Y‖²` using `‖β_{#1}‖² = (u−1)/q + 2` (`betaGrid_norm`), the Dade isometry
`‖τ_S β‖² = ‖β‖²` on `A₀(S)`-support (`dadeIntegralCharacterMap_inner_eq_on_supported_span`), and the
decomposition `β_{#1} = Γ − η_{01} + 1_G` with the `η_{01}`/`1_G` orthogonalities peeled off, then
splits off the grid-projection `X` (a `≠ 0` combination of the `η_{ik}`, whence the `X + Y` framing —
`‖Γ‖²` itself is **not** bounded, correcting the earlier `Re⟨Γ,Γ⟩ ≤ (u−1)/q + 1` overstatement,
issue 3003).  It needs the (13.18.a,c) orthogonalities plus the on-support isometry, hence gated on
the same `A₀(S)` normedTI content. -/
theorem gammaGrid_Y_norm_bound [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (X Y : ClassFunction G ℂ), GammaGrid hG hyp = X + Y →
        ClassFunction.inner X Y = 0 →
        (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
        (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) := sorry

/-- **Faithful §13 producer for Peterfalvi (13.18).**  The (13.18) virtual characters `β_j`/`Γ`
and their genuine properties (support (13.18.a), the (13.18.b) norm `‖β_j‖² = (u−1)/q + 2`,
orthogonality of `Γ` to `1_G`, reality, and the (13.18.d) `‖Y‖²` residual bound) are supplied here.
The concrete `β_j = betaGrid hyp j` and `Γ = GammaGrid hG hyp` are built from the honest `S`-side
Dade isometry `τ_S` (`hyp.dadeHypS0`, **not** the `= 0` placeholder `hyp.tauS`) and the induced
trivial character `Ind_{PW₁}^S 1`.  The bundled properties are the precisely-isolated §13 obligations
`betaGrid_support` / `betaGrid_norm` / `gammaGrid_orthogonal_one` / `gammaGrid_real` /
`gammaGrid_Y_norm_bound`; the (13.18.c) `j`-independence is the standalone `gammaGrid_defGamma`
(proven, modulo the (4.8)/(5.3) cross-relation `tauS_mu_row0_cross`).  Their deep content bottoms out
at the (13.2.e) `A₀(S)` normedTI Dade=Ind bridge, the (5.3) `S`↔`W` Dade cross-relation, and the
Frobenius norm `norm_induce_one_frobenius`. -/
noncomputable def betaData_of_grid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    BetaData hyp where
  j := j
  j_ne_zero := hj
  beta := betaGrid hyp j
  Gamma := GammaGrid hG hyp
  support_formula := betaGrid_support hG hyp j hj
  norm_formula := betaGrid_norm hG hyp j hj
  Gamma_orthogonal_one := gammaGrid_orthogonal_one hG hyp
  Gamma_real := gammaGrid_real hG hyp
  Y_norm_bound := gammaGrid_Y_norm_bound hG hyp

/-- **Peterfalvi (13.18)**: the virtual character `beta_j` has controlled
support, norm, and orthogonal remainder.

De-opacified (W3 §15): the conclusions are the genuine (13.18) statements — `β_j`'s support
control (13.18.a), the (13.18.b) norm `‖β_j‖² = (u−1)/q + 2`, and the residual `Γ`'s orthogonality
to `1_G` (13.18.c), reality (13.18.c), and the (13.18.d) `‖Y‖²` bound — each about the produced
characters `data.beta`/`data.Gamma`.  They are the genuine fields of the faithful producer
`betaData_of_grid`; the (13.18.b) Frobenius induced-trivial norm half is the already-proven
`norm_induce_one_frobenius`.  The (13.18.c) `j`-independence half is the standalone
`gammaGrid_defGamma` (kept separate to avoid mixing the `FiniteInduce` `τ_S` instances with the
explicit inner-product instance binders here).  (The earlier grid-orthogonality and `‖Γ‖²`
conjuncts were overstatements — issue 3003.) -/
theorem beta_support_norm_and_remainder [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    ∃ data : BetaData hyp,
      (data.beta.support ⊆ ⋃ (i : Fin hyp.q), (hyp.mu i data.j).support) ∧
        (∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
          ClassFunction.inner data.beta data.beta
            = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)) ∧
        (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
          ClassFunction.inner data.Gamma
            (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0) ∧
        data.Gamma.conj = data.Gamma ∧
        (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
          ∀ (X Y : ClassFunction G ℂ), data.Gamma = X + Y →
            ClassFunction.inner X Y = 0 →
            (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
            (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ)) := by
  -- The principal index `j = 1` (nonzero, using `p ≥ 3`).
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  refine ⟨betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp),
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).support_formula,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).norm_formula,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).Gamma_orthogonal_one,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).Gamma_real,
    (betaData_of_grid _hG hyp ⟨1, by omega⟩ (by simp)).Y_norm_bound⟩

/-- The parity conclusion in Peterfalvi (13.19.c2): the character inner
product is an odd integer, recorded inside `ℂ`. -/
def OddIntegerInner (χ ψ : ClassFunction G ℂ) : Prop :=
  ∃ n : ℤ, Odd n ∧
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)], ClassFunction.inner χ ψ = (n : ℂ)

/-- Carrier for the type-I comparison in Peterfalvi (13.19). -/
structure TypeIOrthogonalityData (hyp : Hypothesis (G := G)) (L : Subgroup G) where
  typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L
  e : ℕ
  e_eq_index : Prop
  Lset : Set (ClassFunction ↥L ℂ)
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  phi : ClassFunction ↥L ℂ
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaL : ClassFunction G ℂ
  betaS : ClassFunction G ℂ
  disjoint_support : Prop
  Ltau_orthogonal_eta : Prop
  betaL_eta_independent : Prop
  caseC1 : Prop
  caseC2 : Prop
  caseC2_eta0j_odd :
    caseC2 →
      ∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
  caseC1_bound :
    caseC1 →
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))
  caseC1_dual : Prop
  caseC2_dual : Prop
  caseC2_dual_etai0_odd :
    caseC2_dual →
      ∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
  caseC1_dual_bound :
    caseC1_dual →
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))

namespace TypeIOrthogonalityData

/-- **Peterfalvi (13.19.c)**, consumer form: any strict gap beyond the
case-(c1) bound forces the parity alternative (c2). -/
theorem caseC2_of_gap {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L)
    (hcases : data.caseC1 ∨ data.caseC2)
    (hgap :
      ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ) <
        ((Nat.card ↥data.typeISetup.H - 1 : ℕ) : ℚ) / (data.e : ℚ)) :
    data.caseC2 := by
  rcases hcases with hcaseC1 | hcaseC2
  · exact False.elim ((not_lt_of_ge (data.caseC1_bound hcaseC1)) hgap)
  · exact hcaseC2

/-- **Peterfalvi (13.19.c)** after swapping `S` and `T`: any strict gap beyond
`(v - 1) / p` excludes the dual case-(c1) bound and forces the dual parity
alternative (c2), the source of the `eta_i0` congruences. -/
theorem caseC2_dual_of_gap {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L)
    (hcases : data.caseC1_dual ∨ data.caseC2_dual)
    (hgap :
      ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ) <
        ((Nat.card ↥data.typeISetup.H - 1 : ℕ) : ℚ) / (data.e : ℚ)) :
    data.caseC2_dual := by
  rcases hcases with hcaseC1 | hcaseC2
  · exact False.elim ((not_lt_of_ge (data.caseC1_dual_bound hcaseC1)) hgap)
  · exact hcaseC2

/-- **Peterfalvi (13.19.c2)**: once both S- and T-side parity alternatives
hold, the two zero-axis families of `eta` have odd integer inner product with
`beta_L`. -/
theorem eta_axes_odd_of_caseC2_pair {hyp : Hypothesis (G := G)} {L : Subgroup G}
    (data : TypeIOrthogonalityData hyp L) (hcases : data.caseC2 ∧ data.caseC2_dual) :
    (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner data.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧
      (∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner data.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) := by
  exact ⟨data.caseC2_eta0j_odd hcases.1, data.caseC2_dual_etai0_odd hcases.2⟩

end TypeIOrthogonalityData

/-- **Faithful §13 grid/Dade producer for Peterfalvi (13.19).**

Given a type-I maximal subgroup `L` with its (12.1) `S14.Hypothesis` `typeISetup`, this bundles the
genuinely grid-dependent data and facts of (13.19) against a concrete kernel index `e`, family
`Lset` and generator `phi`:

* the Dade images `β_L`, `β_S`, disjoint-supported (13.18.a-style);
* `phi ∈ Lset` of degree `e = |L : H|`;
* **(13.19.a)** `L^{τ₁} ⊥ {η_ij}` and `β_L ⊥ {η_ij}` (grid orthogonality, the `Ltau_orthogonal_eta`
  / `betaL_eta_independent` content), bottoming out at the (3.9) `τ`-isometry (σ-pinned);
* **(13.19.c)** the S- and T-side dichotomies `caseC1 ∨ caseC2` where `caseC1` is the rational
  degree bound `(|H|−1)/e ≤ (u−1)/q` and `caseC2` is the genuine `η`-axis odd-integer parity
  `∀ j ≠ 0, ⟨β_L, η_0j⟩ ∈ 2ℤ+1` (dual: `(v−1)/p`, `η_i0`).

Everything grid-dependent is isolated here; the assembling theorem
`typeI_orthogonality_dichotomy` supplies the honest §14 `typeISetup`, the `τ₁ = typeISetup.tau`
Dade map, and reads the dichotomy implication fields off as identities (no over-claim). -/
structure TypeIOrthogonalityGridData (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) where
  e : ℕ
  e_eq_index : ((maxNilpotentNormalHall L).subgroupOf L).index = e
  Lset : Set (ClassFunction ↥L ℂ)
  phi : ClassFunction ↥L ℂ
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaL : ClassFunction G ℂ
  betaS : ClassFunction G ℂ
  /-- The T-side companion `β_T^τ` (the S↔T-swapped `β_S^τ`), pairing with `φ^{τ₁}` in the dual
  (13.19.c1) parity. -/
  betaT : ClassFunction G ℂ
  disjoint_support : Disjoint betaL.support betaS.support
  /-- **(13.19)**: `β_L` is the Dade image `β_L^τ = (Ind_H^L 1_H − φ)^{τ₁}` (the extension
  `τ₁ = typeISetup.tau` agrees with `τ` on the `A(L)`-supported `Ind_H^L 1_H − φ`). -/
  betaL_eq :
    ∀ [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
      [Invertible (Nat.card ↥((typeISetup.H).subgroupOf L) : ℂ)],
      betaL = typeISetup.tau
        (ClassFunction.induce ((typeISetup.H).subgroupOf L)
          (trivialClassFunction ↥((typeISetup.H).subgroupOf L)) - phi)
  Ltau_orthogonal_eta :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.q) (j : Fin hyp.p),
        ClassFunction.inner (typeISetup.tau phi) (hyp.eta i j) = 0
  /-- **(13.19.c)**, first clause: `(β_L^τ, η_{0j})` is independent of `j` for `1 ≤ j < p`. -/
  betaL_eta0_row_constant :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
        ClassFunction.inner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
          = ClassFunction.inner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j')
  /-- **(13.19.c)**, first clause after the S↔T swap: `(β_L^τ, η_{i0})` is independent of `i`
  for `1 ≤ i < q`. -/
  betaL_eta0_col_constant :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
        ClassFunction.inner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
          = ClassFunction.inner betaL (hyp.eta i' ⟨0, hyp.p_prime.pos⟩)
  /-- **(13.19.c)** S-side dichotomy, faithful form: **(c1)** `(β_S^τ, φ^{τ₁}) ≡ 1 (mod 2)` and
  the degree bound `(|H|−1)/e ≤ (u−1)/q`, or **(c2)** the `η_{0j}` odd-parity and `p ≤ e`. -/
  caseC :
    (OddIntegerInner betaS (typeISetup.tau phi) ∧
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))) ∨
      ((∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧ hyp.p ≤ e)
  /-- **(13.19.c)** T-side (S↔T swapped) dichotomy, faithful form: **(c1)**
  `(β_T^τ, φ^{τ₁}) ≡ 1 (mod 2)` and `(|H|−1)/e ≤ (v−1)/p`, or **(c2)** the `η_{i0}` odd-parity
  and `q ≤ e`. -/
  caseC_dual :
    (OddIntegerInner betaT (typeISetup.tau phi) ∧
      (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))) ∨
      ((∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧ hyp.q ≤ e)

/-- **Faithful §13 producer for Peterfalvi (13.19).**  The grid/Dade data and facts of (13.19) for a
type-I maximal `L` with its (12.1) Hypothesis `typeISetup`.  The construction is the §3/§4/§5
Dade-isometry layer for `L` (the (3.9) `τ`-isometry, σ-pinned via `S05_IntegralSigma`, giving the
`η`-grid orthogonality) plus the (13.19.c) degree/parity dichotomy from the coherence bounds; this is
the single isolated deep obligation.  Mirrors the `betaData_of_grid` / `betaM_expansion_data`
producer pattern. -/
noncomputable def typeIOrthogonalityGridData_of_typeISetup [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    TypeIOrthogonalityGridData hyp typeISetup := sorry

/-- **Peterfalvi (13.19)**: a type-I maximal subgroup has `𝓛^{τ₁}` orthogonal to the `eta_ij`,
`(β_L^τ, η_{0j})` constant along each zero axis, and on each zero axis one of the two (13.19.c)
cases — the faithful conjunction forms `(c1) = parity ∧ degree bound` and
`(c2) = η-axis odd-parity ∧ p ≤ e` — holds.

De-opacified (W3 §15): the honest §14 content — the (12.1) `S14.Hypothesis` of `L`
(`S14.exists_typeI_hypothesis`) and its genuine Dade map `τ₁ = typeISetup.tau` — is constructed here;
the opaque `Prop` fields of `TypeIOrthogonalityData` are instantiated to the **genuine** (13.19)
statements.  `betaL_eta_independent` is instantiated to the faithful (13.19.c) first clause — the
zero-axis **constancy** of `(β_L^τ, η_{0j})`/`(β_L^τ, η_{i0})` (NOT orthogonality: in case (c2)
these inner products are odd).  The dichotomy implication fields (`caseC1_bound`,
`caseC2_eta0j_odd`, dual) are the conjunction projections.  The grid-dependent atoms come from the
faithful producer `typeIOrthogonalityGridData_of_typeISetup`, whose type is the genuine (13.19)
grid content. -/
theorem typeI_orthogonality_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L) :
    ∃ data : TypeIOrthogonalityData hyp L,
      data.disjoint_support ∧ data.Ltau_orthogonal_eta ∧
        data.betaL_eta_independent ∧
          (data.caseC1 ∨ data.caseC2) ∧
            (data.caseC1_dual ∨ data.caseC2_dual) := by
  -- (12.1)/(14.*): the type-I maximal `L` carries a genuine `S14.Hypothesis` (honest own-logic).
  obtain ⟨typeISetup⟩ := OddOrder.Peterfalvi.S14.exists_typeI_hypothesis _hG hLmax hLI
  -- The grid/Dade atoms and facts (the single deep obligation).
  let g := typeIOrthogonalityGridData_of_typeISetup _hG hyp typeISetup
  -- Assemble `TypeIOrthogonalityData` with the genuine opaque-`Prop` choices and
  -- conjunction-projection dichotomy implication fields.
  refine ⟨{ typeISetup := typeISetup
            e := g.e
            e_eq_index := ((maxNilpotentNormalHall L).subgroupOf L).index = g.e
            Lset := g.Lset
            tau1 := typeISetup.tau
            phi := g.phi
            phi_mem := g.phi_mem
            phi_degree_eq_e := g.phi_degree_eq_e
            betaL := g.betaL
            betaS := g.betaS
            disjoint_support := Disjoint g.betaL.support g.betaS.support
            Ltau_orthogonal_eta :=
              ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (i : Fin hyp.q) (j : Fin hyp.p),
                  ClassFunction.inner (typeISetup.tau g.phi) (hyp.eta i j) = 0
            betaL_eta_independent :=
              (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
                  ClassFunction.inner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
                    = ClassFunction.inner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j')) ∧
              (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
                  ClassFunction.inner g.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
                    = ClassFunction.inner g.betaL (hyp.eta i' ⟨0, hyp.p_prime.pos⟩))
            caseC1 :=
              OddIntegerInner g.betaS (typeISetup.tau g.phi) ∧
                (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                  ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))
            caseC2 :=
              (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧ hyp.p ≤ g.e
            caseC2_eta0j_odd := fun h => h.1
            caseC1_bound := fun h => h.2
            caseC1_dual :=
              OddIntegerInner g.betaT (typeISetup.tau g.phi) ∧
                (((Nat.card ↥typeISetup.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                  ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))
            caseC2_dual :=
              (∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧ hyp.q ≤ g.e
            caseC2_dual_etai0_odd := fun h => h.1
            caseC1_dual_bound := fun h => h.2 },
    g.disjoint_support, g.Ltau_orthogonal_eta,
    ⟨g.betaL_eta0_row_constant, g.betaL_eta0_col_constant⟩, g.caseC, g.caseC_dual⟩

end OddOrder.Peterfalvi.S15

