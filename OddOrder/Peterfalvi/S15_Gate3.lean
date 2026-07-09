/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_SAndTBasic

/-!
# S15_Gate3

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ### (13.17) gate 3/4 structural inputs (issue 2013)

The two structural facts that the type-II rule-out of (13.17.a/b) reads off the `§13`/`§14`
machinery but that the bare `Hypothesis` does not pin.  Both are declared here as faithful
sorried producers (the gate-2 pattern of `coprime_card_U_card_P_of_disjoint`): their proofs are
gated on the genuine §13 counting (`card_Q_eq`, B1) and on BG Theorem E
(`card_LF_coprime_pq`, B2), but their *statements* let the structural cores of the `L ~ T` and
type-`I` branches of `exists_typeI_maximal_overNormalizer_U` be discharged sorry-free.  See
issue 2013 / `notes/peterfalvi/s13_17_structural_program.md`. -/

/-- **Peterfalvi (13.17.a) T-side Fitting order (B1)**: `|Q| = |T_F| = q^p`.

This is the `S ↔ T` symmetric companion of `BasicStructureData.P_order` (`|P| = |S_F| = p^q`), now
**proven** for the (14.9) type-II member `T`: from `IsTypeII T`, the (9.3) Wielandt order relation
`typeII_III_IV_order_relations` on the reconciled type-`P` data of `T` (`reconciled_typePData_T`)
gives `|T_F| = |tpd.W2|^|tpd.W1| = |W₁|^|W₂| = q^p` (the intrinsic factors reconcile to `tpd.W2 = W₁`,
`tpd.W1 = W₂`).  Combined with the automorphism-equivariance of `M_F`
(`maxNilpotentNormalHall_pointwise_smul`), it gives `|L_F| = q^p` for every `L` conjugate to `T`,
which is what the `L ~ T` exclusion of (13.17.a) uses.  The `IsTypeII T` hypothesis is threaded from
`exists_LHypothesis` (§16, via the (14.9) `T_typeII`). -/
theorem card_Q_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  obtain ⟨tpd, _htpdV, htpdW1, htpdW2⟩ := reconciled_typePData_T hG hyp
  have tdata : TypeIIData hyp.T := hTTypeII.some
  have hUne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hW1prime : (Nat.card ↥tpd.W1).Prime := by
    rw [htpdW1, ← hyp.p_eq_card_W2]; exact hyp.p_prime
  have hTI := tdata.common.2.2
  have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
    { maximal := hyp.T_maximal
      typeP := tpd
      nontrivial := ⟨hUne, hW1prime, hTI⟩
      type_alt := Or.inl hTTypeII }).1 hTTypeII
  have hord2 : Nat.card ↥tpd.H = Nat.card ↥tpd.W2 ^ Nat.card ↥tpd.W1 := hord.2
  have hW2card : Nat.card ↥tpd.W2 = hyp.q := by
    rw [htpdW2, ← hyp.q_eq_card_W1]
  rw [tpd.H_eq, ← hyp.Q_eq_TF, hW2card, htpdW1, ← hyp.p_eq_card_W2] at hord2
  exact hord2

/-- **Peterfalvi (13.17.a), `T`-conjugate Fitting order** — the **proven** part (1) of
`tConjugate_fitting_data`: for `L` conjugate to `T` (`conj g • L = T`), `|L_F| = q^p`.

`M_F` is automorphism-equivariant (`maxNilpotentNormalHall_pointwise_smul`), so
`conj g • L_F = maxNilpotentNormalHall (conj g • L) = maxNilpotentNormalHall T = Q`; conjugation
preserves cardinality, so `|L_F| = |Q| = q^p` (`card_Q_eq`, now proven for the (14.9) type-II `T`). -/
theorem tConjugate_card_LF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    {L : Subgroup G} {g : G} (hconj : MulAut.conj g • L = hyp.T) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.q ^ hyp.p := by
  have hMF : MulAut.conj g • maxNilpotentNormalHall L = hyp.Q := by
    rw [maxNilpotentNormalHall_pointwise_smul, hconj, ← hyp.Q_eq_TF]
  have hcard : Nat.card ↥(maxNilpotentNormalHall L) = Nat.card ↥hyp.Q := by
    rw [← hMF]
    exact Nat.card_congr
      (Subgroup.equivSMul (MulAut.conj g) (maxNilpotentNormalHall L)).toEquiv
  rw [hcard]; exact card_Q_eq hG hyp hTTypeII

/-- **Peterfalvi (13.17.a) T-conjugate Fitting structure**: for a maximal subgroup `L` conjugate
to `T` (`conj g • L = T`), the Fitting kernel `L_F` is a `q`-group of order `q^p` that contains
the cyclic factor `W₁` and meets the complement `U` trivially.

* `|L_F| = q^p` is the transfer of `card_Q_eq` (B1) along `maxNilpotentNormalHall_pointwise_smul`;
* `W₁ ≤ L_F` holds because `W₁ ⊆ N_G(U) ⊆ L` is a `q`-subgroup of `L` and `L_F` is the
  normal `q`-Hall subgroup (Pf p.81 "as `W₁ ⊆ N_G(U) ⊆ L`, `W₁ ⊆ H`");
* `L_F ⊓ U = 1` because `L_F` is a `q`-group while `|U| = u` is prime to `q` (Pf (13.2.a)).

These are exactly the three facts the `L ~ T` branch of (13.17.a) consumes before deriving
`[U, W₁] ⊆ L_F ⊓ U = 1` against the `U W₁` Frobenius structure.  The `card`-equality part is
the isolated §13 residual (`card_Q_eq`); `W₁ ≤ L_F` and `L_F ⊓ U = ⊥` are the §13.2-level
structural data.  **Now proven**: part (1) is `tConjugate_card_LF` (via `card_Q_eq`); part (2)
`W₁ ≤ L_F` places the `q`-group `W₁ ⊆ N_G(U) ⊆ L` in the normal `q`-Hall `L_F`
(`pgroup_le_of_normal_coprime_index`); part (3) `L_F ⊓ U = ⊥` from `|L_F| = q^p` coprime to `|U|`
(the `U ⋊ W₁` Frobenius gives `(|U|, q) = 1`).  `IsTypeII T` is threaded from
`exists_typeI_maximal_overNormalizer_U` (via (14.9) `T_typeII`); `hNUL` is the `N_G(U) ⊆ L` context. -/
theorem tConjugate_fitting_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    {L : Subgroup G} {g : G} (hconj : MulAut.conj g • L = hyp.T)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.q ^ hyp.p ∧
      hyp.W1 ≤ maxNilpotentNormalHall L ∧
      maxNilpotentNormalHall L ⊓ hyp.U = ⊥ := by
  have hLFcard : Nat.card ↥(maxNilpotentNormalHall L) = hyp.q ^ hyp.p :=
    tConjugate_card_LF hG hyp hTTypeII hconj
  -- `W₁ ⊆ N_G(U) ⊆ L`.
  have hW1leL : hyp.W1 ≤ L := hyp.W1_normalizes_U.trans hNUL
  -- part 2: `W₁ ≤ L_F` — `W₁` is a `q`-group in `L`, `L_F` the normal `q`-Hall subgroup.
  have hW1leLF : hyp.W1 ≤ maxNilpotentNormalHall L := by
    refine pgroup_le_of_normal_coprime_index (S := L) hyp.q_prime hW1leL
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L) ?_ ?_ ?_
    · have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall L
      have hcard_eq : Nat.card ↥((maxNilpotentNormalHall L).subgroupOf L)
          = Nat.card ↥(maxNilpotentNormalHall L) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L)).toEquiv
      exact hcard_eq ▸ Ch03.IsHallSubgroup.coprime_index hHall
    · rw [hLFcard]; exact dvd_pow_self hyp.q hyp.p_prime.pos.ne'
    · intro w hw
      have heq : orderOf (⟨w, hw⟩ : ↥hyp.W1) = orderOf w :=
        (orderOf_injective hyp.W1.subtype Subtype.coe_injective ⟨w, hw⟩).symm
      have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W1) ∣ Nat.card ↥hyp.W1 := orderOf_dvd_natCard _
      rw [heq, ← hyp.q_eq_card_W1] at h1
      exact h1
  -- part 3: `L_F ⊓ U = ⊥` — `L_F` a `q`-group (`|L_F| = q^p`), `U` coprime to `q` (`U ⋊ W₁` Frobenius).
  have hLFU : maxNilpotentNormalHall L ⊓ hyp.U = ⊥ := by
    obtain ⟨data, _⟩ := basic_structure hG hyp
    have hcopUq : Nat.Coprime (Nat.card ↥hyp.U) hyp.q := by
      have hk := data.UW1_frobenius.coprime_card_kernel_complement
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
        ← hyp.q_eq_card_W1] at hk
      exact hk
    have hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (Nat.card ↥hyp.U) := by
      rw [hLFcard]; exact hcopUq.symm.pow_left hyp.p
    exact Subgroup.inf_eq_bot_of_coprime hcop
  exact ⟨hLFcard, hW1leLF, hLFU⟩

/-- **Peterfalvi (8.17.a) coprimality (B2)**: for a type-`I` maximal subgroup `L` that is *not*
conjugate to `S` or to `T`, the Fitting kernel order `|L_F|` is prime to `p q`.

*Derivation (Pf p.82 "(8.17.a)"):* `bgTheoremE_cover_data` (Peterfalvi (8.17), `:= sorry`,
BG Theorem E) exhibits representatives `M_i` of the conjugacy classes of maximal subgroups with
`π((M_i)_s)` pairwise disjoint (`BGTheoremECoverData.primeFactors_disjoint`).  For type `I`,
`(M_i)_s = M_F` (`mainSubgroup … .I = maxNilpotentNormalHall`); since `p ∈ π(S_s)` and
`q ∈ π(T_s)` while `L` is non-conjugate to either, `π(L_F)` is disjoint from `{p, q}`, i.e.
`Coprime |L_F| (p q)`.  Both the derivation *and* its `bgTheoremE_cover_data` cite are
§10/BG-gated;
declared here `:= sorry` as the isolated residual of gate 4 (the BG Theorem E content lives in
`bgTheoremE_cover_data`, owner = F).  This is exactly the input the type-`I` branch of (13.17.b)
reads off before deducing `W₁ ∩ L_F = 1` and running the (9.1) fixed-point-free argument. -/
theorem card_LF_coprime_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (_hLmax : L ∈ maximalSubgroups G)
    (_hLI : IsTypeI L) (_hLnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S)
    (_hLnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T) :
    Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (hyp.p * hyp.q) := sorry

/-- **Frobenius-kernel self-centralizing (the gate-4 final step)**: in a finite Frobenius group `L`
with kernel `N`, any abelian subgroup `U` meeting `N` nontrivially lies in `N`.  Picking
`1 ≠ x ∈ U ⊓ N`, every `u ∈ U` commutes with `x` (`U` abelian), so `u ∈ C_L(x) ≤ N`
(`IsFrobeniusGroup.centralizer_kernel_le`: the centralizer of a nontrivial kernel element lies in
the kernel).  This is exactly the `U ⊆ C_L(U ∩ L_F) ⊆ L_F` deduction of Peterfalvi (13.17.b) once
`U ∩ L_F ≠ 1` is known.  General group theory; reusable, hoistable to `Ch06`. -/
theorem le_kernel_of_isMulCommutative_of_inf_ne_bot {L : Type*} [Group L] [Finite L]
    {N A U : Subgroup L} (h : Ch06.IsFrobeniusGroup L N A)
    (hUab : IsMulCommutative ↥U) (hinf : U ⊓ N ≠ ⊥) : U ≤ N := by
  obtain ⟨x, hxmem, hxne⟩ := (U ⊓ N).bot_or_exists_ne_one.resolve_left hinf
  have hxU : x ∈ U := (Subgroup.mem_inf.mp hxmem).1
  have hxN : x ∈ N := (Subgroup.mem_inf.mp hxmem).2
  have hcent := h.centralizer_kernel_le x hxN hxne
  intro u hu
  refine hcent (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  exact congrArg Subtype.val (hUab.is_comm.comm ⟨u, hu⟩ ⟨x, hxU⟩)

/-- **Type is conjugacy-invariant** (the (13.17.a/b) `L ~ S`/`L ~ T` rule-out): a type-`I` maximal
subgroup `L` is not conjugate to any non-type-`I` maximal subgroup `M`.  If `conj g • L = M` then
`M` would be type `I` (`isTypeI_of_conj`, the automorphism-equivariance of the Peterfalvi taxonomy
— `OddOrder.GroupTheory.MaximalSubgroupTypeConj`), contradicting
`not_isTypeI_of_isTypeNonI`.  This is **gate-4 piece 1**, now discharged (sorry-free, axiom-clean);
reusable across the §16 conjugacy arguments. -/
theorem not_conj_of_isTypeI_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L M : Subgroup G} (hLI : IsTypeI L) (hMmax : M ∈ maximalSubgroups G)
    (hMnonI : IsTypeNonI M) : ¬ ∃ g : G, MulAut.conj g • L = M :=
  fun ⟨g, hg⟩ =>
    OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG hMmax hMnonI
      (OddOrder.GroupTheory.isTypeI_of_conj hLI hg)

/-- **Peterfalvi (13.17.b), the (9.1) fixed-point-free residual (gate-4 pieces 4–6)**: once the
(8.17.a) coprimality `|L_F| ⟂ p q` is in hand for the type-`I` `L` over `N_G(U)`, the complement
`U` lies in the Fitting kernel `L_F`.  As `|W₁| = q ∤ |L_F|`, `W₁ ∩ L_F = 1`; were `U ∩ L_F = 1`,
the Frobenius group `U W₁ ⊆ L` (from (13.2.a)) would act fixed-point-freely on `L_F`
(`U, W₁ ≤ L ≤ N_G(L_F)`, a coprime action), so Wielandt's formula (9.1)
`wielandt_fixedPoint_frobenius` would force `|L_F| = 1`, against type-`I` `L_F ≠ 1`
(`TypeFData.H_nontrivial`); hence `U ∩ L_F ≠ 1` and `U ⊆ C_L(U ∩ L_F) ⊆ L_F`
(`le_kernel_of_isMulCommutative_of_inf_ne_bot`).  The isolated deep residual of gate 4: the
`CoprimeFrobeniusAction (U W₁) (L_F)` construction plus the (still sorried) Wielandt formula.
`:= sorry`; see issue 2009 / `notes/peterfalvi/s13_17_structural_program.md`. -/
theorem typeI_U_le_fitting_of_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hSTypeII : IsTypeII hyp.S) {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (hyp.p * hyp.q)) :
    hyp.U ≤ maxNilpotentNormalHall L := by
  -- The (12.7) Frobenius structure of the type-`I` `L`, with kernel `L_F = maxNilpotentNormalHall L`.
  obtain ⟨frob, _⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hLmax hLI
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hfrobLF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((maxNilpotentNormalHall L).subgroupOf L) frob.complement := hHeq ▸ frob.frobenius
  have hUleL : hyp.U ≤ L := Subgroup.le_normalizer.trans hNUL
  have hW1leL : hyp.W1 ≤ L := hyp.W1_normalizes_U.trans hNUL
  have hLFleL : maxNilpotentNormalHall L ≤ L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  obtain ⟨bdata, _⟩ := basic_structure hG hyp
  have hsolv : IsSolvable ↥(maxNilpotentNormalHall L) := by
    haveI := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
    exact IsNilpotent.to_isSolvable
  -- piece 3: `W₁ ⊓ L_F = ⊥`, since `q = |W₁|` divides `p q` and `|L_F| ⟂ p q`.
  have hcopLFq : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.q :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left hyp.q hyp.p) hcop
  have hW1LF : hyp.W1 ⊓ maxNilpotentNormalHall L = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (by rw [← hyp.q_eq_card_W1]; exact hcopLFq.symm)
  -- piece 5: `U ⊓ L_F ≠ ⊥` (else the Frobenius `U W₁` acts fixed-point-freely on `L_F`).
  have hUmeets : hyp.U ⊓ maxNilpotentNormalHall L ≠ ⊥ := by
    intro hbot
    have hcopU : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hUleL hfrobLF hbot
    have hcopW1 : Nat.Coprime (Nat.card ↥hyp.W1) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hW1leL hfrobLF hW1LF
    have hcardUW1 : Nat.card ↥(hyp.U ⊔ hyp.W1) = Nat.card ↥hyp.U * Nat.card ↥hyp.W1 := by
      rw [← bdata.UW1_frobenius.isComplement.card_mul,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    have hcopUW1 : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (Nat.card ↥(hyp.U ⊔ hyp.W1)) := by
      rw [hcardUW1]; exact Nat.Coprime.mul_right hcopU.symm hcopW1.symm
    have hLFbot : maxNilpotentNormalHall L = ⊥ :=
      OddOrder.GroupTheory.isFrobenius_kernel_eq_bot_of_frobenius_subgroup hLFleL
        (sup_le hUleL hW1leL) ⟨frob.complement, hfrobLF⟩ bdata.UW1_frobenius hbot hW1LF hsolv hcopUW1
    exact frob.frobenius.ne_bot_kernel (by rw [hHeq, hLFbot, Subgroup.bot_subgroupOf])
  -- piece 6: `U ⊆ C_L(U ∩ L_F) ⊆ L_F` since `U` is abelian and `L_F` is the Frobenius kernel.
  have hUab : IsMulCommutative ↥(hyp.U.subgroupOf L) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hUleL).symm (isMulCommutative_U hG hyp)
  have hinf : (hyp.U.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L) ≠ ⊥ := by
    rw [show (hyp.U.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L)
        = (hyp.U ⊓ maxNilpotentNormalHall L).subgroupOf L from (Subgroup.comap_inf _ _ _).symm]
    intro h
    apply hUmeets
    have hle : hyp.U ⊓ maxNilpotentNormalHall L ≤ L := inf_le_right.trans hLFleL
    rw [← inf_eq_left.mpr hle]
    exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
  have hsub := le_kernel_of_isMulCommutative_of_inf_ne_bot hfrobLF hUab hinf
  calc hyp.U = (hyp.U.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hUleL).symm
    _ ≤ ((maxNilpotentNormalHall L).subgroupOf L).map L.subtype := Subgroup.map_mono hsub
    _ = maxNilpotentNormalHall L := Subgroup.map_subgroupOf_eq_of_le hLFleL

/-- **Peterfalvi (13.17.b) `U ⊆ L_F` for the type-`I` `L`**: when `S` is type II and `L` is a
type-`I` maximal subgroup over `N_G(U)`, the complement `U` lies in the Fitting kernel `L_F`.

*Proof (Pf p.82, the gate-4 structural core):* `L` is non-conjugate to `S` and `T` (it is type `I`
while `S`, `T` are non-I and type is conjugacy-invariant — `not_conj_of_isTypeI_of_isTypeNonI`, the
**discharged gate-4 piece 1**), so (8.17.a) = `card_LF_coprime_pq` (B2) gives `|L_F|` prime to
`p q`, in particular to `q = |W₁|`.  The remaining (9.1) fixed-point-free argument
(`W₁ ∩ L_F = 1`; `U ∩ L_F ≠ 1` by Wielandt; `U ⊆ C_L(U ∩ L_F) ⊆ L_F`) is
`typeI_U_le_fitting_of_coprime` (the isolated deep residual of gate 4).

Assembled `sorry`-free from the piece-1 non-conjugacy, the (8.17.a) coprimality producer
`card_LF_coprime_pq` (owner = F, BG Theorem E), and `typeI_U_le_fitting_of_coprime`. -/
theorem typeI_overNormalizer_U_le_fitting [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (_hSTypeII : IsTypeII hyp.S) {L : Subgroup G} (_hLmax : L ∈ maximalSubgroups G)
    (_hLI : IsTypeI L) (_hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L) :
    hyp.U ≤ maxNilpotentNormalHall L := by
  -- (piece 1) `L` is non-conjugate to `S`, `T` (type is conjugacy-invariant; `S`, `T` are non-I).
  have hnS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG _hLI hyp.S_maximal hyp.S_nonI
  have hnT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG _hLI hyp.T_maximal hyp.T_nonI
  -- (piece 2) the (8.17.a) coprimality, then (pieces 4–6) the isolated FPF residual.
  exact typeI_U_le_fitting_of_coprime _hG hyp _hSTypeII _hLmax _hLI _hNUL
    (card_LF_coprime_pq _hG hyp _hLmax _hLI hnS hnT)

/-- **`T`-side dual of `typeI_U_le_fitting_of_coprime`** (Pf (13.17.b), V-side): for `T` type II and
a type-`I` maximal `L` over `N_G(V)` with `|L_F| ⟂ pq`, the complement `V ⊆ L_F`.  Mirror of the
`U`-side; the `V W₂` Frobenius is built from the reconciled `TypePData T`
(`typeP_uW1_frobenius`) rather than `basic_structure` (which is `S`-side only). -/
theorem typeI_V_le_fitting_of_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L)
    (hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (hyp.p * hyp.q)) :
    hyp.V ≤ maxNilpotentNormalHall L := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW2, _⟩ := reconciled_typePData_T hG hyp
  obtain ⟨frob, _⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hLmax hLI
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hfrobLF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((maxNilpotentNormalHall L).subgroupOf L) frob.complement := hHeq ▸ frob.frobenius
  have hVleL : hyp.V ≤ L := Subgroup.le_normalizer.trans hNVL
  have hW2leL : hyp.W2 ≤ L := hyp.W2_normalizes_V.trans hNVL
  have hLFleL : maxNilpotentNormalHall L ≤ L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  have htpdVne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hVW2frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
        (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
    rwa [htpdV, htpdW2] at h
  have hsolv : IsSolvable ↥(maxNilpotentNormalHall L) := by
    haveI := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
    exact IsNilpotent.to_isSolvable
  have hcopLFp : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.p :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right hyp.p hyp.q) hcop
  have hW2LF : hyp.W2 ⊓ maxNilpotentNormalHall L = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime (by rw [← hyp.p_eq_card_W2]; exact hcopLFp.symm)
  have hVmeets : hyp.V ⊓ maxNilpotentNormalHall L ≠ ⊥ := by
    intro hbot
    have hcopV : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hVleL hfrobLF hbot
    have hcopW2 : Nat.Coprime (Nat.card ↥hyp.W2) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hW2leL hfrobLF hW2LF
    have hcardVW2 : Nat.card ↥(hyp.V ⊔ hyp.W2) = Nat.card ↥hyp.V * Nat.card ↥hyp.W2 := by
      rw [← hVW2frob.isComplement.card_mul,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    have hcopVW2 : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L))
        (Nat.card ↥(hyp.V ⊔ hyp.W2)) := by
      rw [hcardVW2]; exact Nat.Coprime.mul_right hcopV.symm hcopW2.symm
    have hLFbot : maxNilpotentNormalHall L = ⊥ :=
      OddOrder.GroupTheory.isFrobenius_kernel_eq_bot_of_frobenius_subgroup hLFleL
        (sup_le hVleL hW2leL) ⟨frob.complement, hfrobLF⟩ hVW2frob hbot hW2LF hsolv hcopVW2
    exact frob.frobenius.ne_bot_kernel (by rw [hHeq, hLFbot, Subgroup.bot_subgroupOf])
  have hVab : IsMulCommutative ↥(hyp.V.subgroupOf L) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hVleL).symm (isMulCommutative_V hG hyp ⟨tdata⟩)
  have hinf : (hyp.V.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L) ≠ ⊥ := by
    rw [show (hyp.V.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L)
        = (hyp.V ⊓ maxNilpotentNormalHall L).subgroupOf L from (Subgroup.comap_inf _ _ _).symm]
    intro h
    apply hVmeets
    have hle : hyp.V ⊓ maxNilpotentNormalHall L ≤ L := inf_le_right.trans hLFleL
    rw [← inf_eq_left.mpr hle]
    exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
  have hsub := le_kernel_of_isMulCommutative_of_inf_ne_bot hfrobLF hVab hinf
  calc hyp.V = (hyp.V.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hVleL).symm
    _ ≤ ((maxNilpotentNormalHall L).subgroupOf L).map L.subtype := Subgroup.map_mono hsub
    _ = maxNilpotentNormalHall L := Subgroup.map_subgroupOf_eq_of_le hLFleL

/-- **`T`-side dual of `typeI_overNormalizer_U_le_fitting`** (Pf (13.17.b), V-side): for `T` type II
and a type-`I` maximal `L` over `N_G(V)`, `V ⊆ L_F`.  Mirror; cites the (8.17.a) coprimality
`card_LF_coprime_pq` (gated, BG Thm E) and the V-side FPF residual `typeI_V_le_fitting_of_coprime`. -/
theorem typeI_overNormalizer_V_le_fitting [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    hyp.V ≤ maxNilpotentNormalHall L := by
  have hnS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.S_maximal hyp.S_nonI
  have hnT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.T_maximal hyp.T_nonI
  exact typeI_V_le_fitting_of_coprime _hG hyp hTTypeII hLmax hLI hNVL
    (card_LF_coprime_pq _hG hyp hLmax hLI hnS hnT)

/-- **Peterfalvi (13.17.a/b)**: a maximal subgroup `L` over `N_G(U)` (for `S` of type II) is of
type I with `U ⊆ L_F`.  *Proof (Pf pp.81-82):* take any maximal `L ⊇ N_G(U)` (proper since
`U ≠ 1` and `G` is simple).  `L` is not conjugate to `S` (else `N_G(U) ⊆ S`, against
`IsTypeII.normalizer_not_le`) nor to `T` (else `|L_F| = q^p` forces `[U,W₁] ⊆ L_F ∩ U = 1`,
against `U W₁` Frobenius from (13.2.a)), so by (8.8.b4) `L` is type I.  Then `U ⊆ L_F`: (8.17.a)
gives `|L_F|` prime to `q`, so `W₁ ∩ L_F = 1`; were `U ∩ L_F = 1`, `U W₁` would act
fixed-point-freely on `L_F`, forcing `L_F = 1` by (9.1).  The genuine §13 structural obligation
feeding (13.17); see issue 2009.

*Skeleton status (Phase 2):* the assembly is proven — `U ≠ ⊥` (from `fitting_lt_derived`), `N_G(U) ≠ ⊤`
(simplicity), the maximal `L ⊇ N_G(U)`, and the (8.8.b4) trichotomy dispatch, with the type-II
property `N_G(U) ⊄ S` wired in through `not_normalizer_U_le_S ∘ exists_conj_typeP_U_of_coprime ∘
coprime_card_U_card_P_of_disjoint`.  Four documented gates remain: `hdisj` (Phase 0(b) carrier
faithfulness, F-ask `P ⊓ U = ⊥`); the L~S Hall-conjugacy derivation of `N_G(U) ⊆ S`; the L~T
`|L_F| = q^p` exclusion; and `U ⊆ L_F` ((8.17.a)+(9.1)). -/
theorem exists_typeI_maximal_overNormalizer_U [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) (hTTypeII : IsTypeII hyp.T) :
    ∃ L : Subgroup G, L ∈ maximalSubgroups G ∧ IsTypeI L ∧
      Subgroup.normalizer (hyp.U : Set G) ≤ L ∧ hyp.U ≤ maxNilpotentNormalHall L := by
  obtain ⟨tdata⟩ := hSTypeII
  -- The configuration complement meets the Fitting kernel trivially.  Now discharged from the
  -- §16 carrier `hyp.Sdata` (the type-`P` data of `S`, reconciled `Sdata.U = U`, `Sdata.H = P`):
  -- `U` complements `M_F = P` in `M' = [S,S]` (`Sdata.derived_complement`), so `P ⊓ U = ⊥`.
  have hdisj : hyp.P ⊓ hyp.U = ⊥ := by
    have key : hyp.Sdata.H ⊓ hyp.Sdata.U = ⊥ := by
      have hd := disjoint_iff.mp hyp.Sdata.derived_complement.disjoint
      rw [eq_bot_iff]
      rintro x ⟨hxH, hxU⟩
      have hxD : x ∈ derivedInG hyp.S := hyp.Sdata.H_le hxH
      have hmem : (⟨x, hxD⟩ : ↥(derivedInG hyp.S)) ∈
          (hyp.Sdata.H.subgroupOf (derivedInG hyp.S)) ⊓
            (hyp.Sdata.U.subgroupOf (derivedInG hyp.S)) :=
        ⟨Subgroup.mem_subgroupOf.mpr hxH, Subgroup.mem_subgroupOf.mpr hxU⟩
      rw [hd, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      simpa using Subtype.ext_iff.mp hmem
    rw [hyp.P_eq_SF, ← hyp.Sdata.H_eq, ← hyp.Sdata_U_eq]
    exact key
  have hcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P) :=
    coprime_card_U_card_P_of_disjoint hyp tdata hdisj
  -- (Phase 1) the type-II property transferred to `hyp.U`: `N_G(U) ⊄ S`.
  have hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S :=
    not_normalizer_U_le_S _hG hyp tdata (exists_conj_typeP_U_of_coprime _hG hyp tdata hcop)
  -- `U ≠ ⊥` (issue 7008): `U` is `S`-conjugate to `tdata.typeP.U`, which is `≠ ⊥` for type II
  -- (the `TypePNontrivialCore` first conjunct `common.1`); conjugation preserves nontriviality.
  have hUne : hyp.U ≠ ⊥ := by
    obtain ⟨x, _, hUconj⟩ := exists_conj_typeP_U_of_coprime _hG hyp tdata hcop
    rw [hUconj]
    exact mt (pointwise_smul_eq_bot_iff (MulAut.conj x)).mp tdata.common.1
  -- `U ≤ S`, hence `U ≠ ⊤`; then by simplicity `N_G(U) ≠ ⊤`.
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hUleS : hyp.U ≤ hyp.S := (le_sup_right.trans hyp.S_deriv_eq_PU.ge).trans hM'_le_S
  have hUneTop : hyp.U ≠ ⊤ := fun hUtop =>
    (mem_maximalSubgroups.mp hyp.S_maximal).1 (top_le_iff.mp (hUtop ▸ hUleS))
  have hNUtop : Subgroup.normalizer (hyp.U : Set G) ≠ ⊤ := by
    intro hNtop
    haveI hUnormal : (hyp.U).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases _hG.simple.eq_bot_or_eq_top_of_normal hyp.U hUnormal with h | h
    · exact hUne h
    · exact hUneTop h
  -- a maximal subgroup `L ⊇ N_G(U)`.
  obtain ⟨L, hNUL, hLmaximal⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G => K ≠ ⊤) hNUtop
  have hLmem : L ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr ⟨hLmaximal.1, fun b hLb => by
      by_contra hbne
      exact lt_irrefl L (lt_of_lt_of_le hLb (hLmaximal.2 hbne hLb.le))⟩
  -- (8.8.b4) trichotomy: `L` is type I, or conjugate to `S`, or conjugate to `T`.
  rcases hyp.theorem88_caseB L hLmem with hLI | _hLconjS | _hLconjT
  · -- `L` is type I; conclude with `U ⊆ L_F` (Pf (13.17.b)).  The (8.17.a)+(9.1)
    -- FPF structural core — `q ∤ |L_F|` (`card_LF_coprime_pq`), so `W₁ ∩ L_F = 1`;
    -- if `U ∩ L_F = 1` then `U W₁` acts FPF on `L_F`, forcing `L_F = 1` by
    -- `wielandt_fixedPoint_frobenius`, against type-`I` `L_F ≠ 1`; hence `U ∩ L_F ≠ 1` and
    -- `U ⊆ C_L(U ∩ L_F) ⊆ L_F` — is `typeI_overNormalizer_U_le_fitting`.
    exact ⟨L, hLmem, hLI, hNUL,
      typeI_overNormalizer_U_le_fitting _hG hyp ⟨tdata⟩ hLmem hLI hNUL⟩
  · -- `L` conjugate to `S` is excluded (`_hLconjS`): Pf (13.17.a) derives `N_G(U) ⊆ S` from the
    -- Hall conjugacy of `U` in the solvable `S`, contradicting `hNUS`.  The structural argument is
    -- `normalizer_le_of_isHall_subgroupOf_of_conj`; its only `S`-specific input is "`U` is a Hall
    -- subgroup of `S`".  That coprimality `|U| ⟂ [S:U]` is the residual (13.2) Hall-faithfulness
    -- datum: `[S:U] = [S:M']·|P|`, `|U| ⟂ |P|` is `hcop`, and `|U| ⟂ [S:M']` holds because
    -- `[S:M'] = |W₁|` is the order of the cyclic κ(S)-Hall complement of `M'` (Pf's `W₁`),
    -- coprime to `|M'| ⊇ |U|`.  The `W₁ = κ(S)`-Hall identification is the carrier-level fact
    -- supplied at the §16 `Section16MaximalPair` (lane-f) but not pinned by the bare `Hypothesis`;
    -- see issue 2009 / `notes/peterfalvi/s13_17_structural_program.md`.
    obtain ⟨g, hg⟩ := _hLconjS
    -- `[S : U] = |P| · |W₁|` from the carrier complements (`U` complements `P` in `M'`,
    -- `W₁` complements `M'` in `S`); coprimality is `|U| ⟂ |P|` (`hcop`) and `|U| ⟂ |W₁|` (the
    -- Frobenius group `U ⋊ W₁` of (13.2.a), `coprime_card_kernel_complement`).
    have hUhall_cop : Nat.Coprime (Nat.card ↥hyp.U) ((hyp.U.subgroupOf hyp.S).index) := by
      obtain ⟨bdata, _⟩ := basic_structure _hG hyp
      have frobcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.W1) := by
        have h := bdata.UW1_frobenius.coprime_card_kernel_complement
        rwa [Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_left : hyp.U ≤ hyp.U ⊔ hyp.W1)).toEquiv,
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_right : hyp.W1 ≤ hyp.U ⊔ hyp.W1)).toEquiv] at h
      have hPleM' : hyp.P ≤ derivedInG hyp.S := le_sup_left.trans hyp.S_deriv_eq_PU.ge
      have hidxM' : ((derivedInG hyp.S).subgroupOf hyp.S).index = Nat.card ↥hyp.W1 := by
        rw [← hyp.Sdata_W1_eq, ← hyp.Sdata.card_W1_eq_derived_index]
      have hidxP : (hyp.P.subgroupOf (derivedInG hyp.S)).index = Nat.card ↥hyp.U := by
        rw [hyp.P_eq_SF, ← hyp.Sdata.card_U_eq_index, hyp.Sdata_U_eq]
      have hScard : Nat.card ↥hyp.S
          = Nat.card ↥hyp.W1 * (Nat.card ↥hyp.U * Nat.card ↥hyp.P) := by
        have e1 := ((derivedInG hyp.S).subgroupOf hyp.S).index_mul_card
        have e2 := (hyp.P.subgroupOf (derivedInG hyp.S)).index_mul_card
        rw [hidxM', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'_le_S).toEquiv] at e1
        rw [hidxP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleM').toEquiv] at e2
        rw [← e1, ← e2]
      have hidxU := (hyp.U.subgroupOf hyp.S).index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleS).toEquiv] at hidxU
      have hidxUeq : (hyp.U.subgroupOf hyp.S).index = Nat.card ↥hyp.P * Nat.card ↥hyp.W1 := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥hyp.U))
        rw [hidxU, hScard]; ring
      rw [hidxUeq]
      exact hcop.mul_right frobcop
    exact absurd (normalizer_le_of_isHall_subgroupOf_of_conj
        (_hG.solvable_of_mem_maximalSubgroups hyp.S_maximal) hUleS
        (isHall_subgroupOf_primeFactors_of_coprime_index hUleS hUhall_cop) hg hNUL) hNUS
  · -- `L` conjugate to `T` is excluded (`_hLconjT`): `|L_F| = q^p` forces `W₁ ⊆ L_F` and
    -- `[U,W₁] ⊆ L_F ∩ U = 1`, contradicting the `U W₁` Frobenius structure (13.2.a).
    exfalso
    obtain ⟨g, hg⟩ := _hLconjT
    -- (B1, `tConjugate_fitting_data`) the T-side Fitting structure of `L_F`:
    -- `|L_F| = q^p`, `W₁ ≤ L_F`, and `L_F ⊓ U = 1`.
    obtain ⟨_hLFcard, hW1le, hLFU⟩ := tConjugate_fitting_data _hG hyp hTTypeII hg hNUL
    -- `U ⊆ L`, hence `U` normalizes `L_F = maxNilpotentNormalHall L`.
    have hUleL : hyp.U ≤ L := Subgroup.le_normalizer.trans hNUL
    have hU_norm_LF : hyp.U ≤ Subgroup.normalizer (maxNilpotentNormalHall L) :=
      hUleL.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L)
    -- `⁅U, W₁⁆ ≤ U` since `W₁` normalizes `U` (`W1_normalizes_U`).
    have hUW1_le_U : ⁅hyp.U, hyp.W1⁆ ≤ hyp.U :=
      OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hyp.W1_normalizes_U
    -- `⁅U, W₁⁆ ≤ ⁅U, L_F⁆ ≤ L_F` since `W₁ ≤ L_F` and `U` normalizes `L_F`.
    have hUW1_le_LF : ⁅hyp.U, hyp.W1⁆ ≤ maxNilpotentNormalHall L := by
      refine (Subgroup.commutator_mono (le_refl hyp.U) hW1le).trans ?_
      rw [Subgroup.commutator_comm]
      exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hU_norm_LF
    -- `⁅U, W₁⁆ ≤ L_F ⊓ U = 1`, so `U` and `W₁` commute elementwise.
    have hUW1_bot : ⁅hyp.U, hyp.W1⁆ = ⊥ :=
      le_bot_iff.mp ((le_inf hUW1_le_LF hUW1_le_U).trans hLFU.le)
    have hUcent : hyp.U ≤ Subgroup.centralizer (hyp.W1 : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUW1_bot
    -- `W₁ ≠ ⊥` (order `q ≥ 2`) and `U ≠ ⊥`: extract nontrivial witnesses contradicting Frobenius.
    have hW1ne : hyp.W1 ≠ ⊥ := by
      intro hbot
      have : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hbot, Subgroup.card_bot]
      exact hyp.q_prime.one_lt.ne' this
    obtain ⟨w, hwW1, hwne⟩ := (hyp.W1.bot_or_exists_ne_one).resolve_left hW1ne
    obtain ⟨n, hnU, hnne⟩ := (hyp.U.bot_or_exists_ne_one).resolve_left hUne
    -- `w * n * w⁻¹ = n` from the commuting (centralizer) relation.
    have hcomm : w * n * w⁻¹ = n := by
      have := hUcent hnU w hwW1
      -- `this : w * n = n * w`; rearrange to `w * n * w⁻¹ = n`.
      rw [mul_inv_eq_iff_eq_mul, this]
    -- Move to the Frobenius group `↥(U ⊔ W₁)` and contradict `conj_frobenius`.
    obtain ⟨bdata, _⟩ := basic_structure _hG hyp
    have hwUW1 : w ∈ hyp.U ⊔ hyp.W1 := Subgroup.mem_sup_right hwW1
    have hnUW1 : n ∈ hyp.U ⊔ hyp.W1 := Subgroup.mem_sup_left hnU
    have hwmem : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1) := hwW1
    have hnmem : (⟨n, hnUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ∈ hyp.U.subgroupOf (hyp.U ⊔ hyp.W1) := hnU
    have hwne' : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hwne (congrArg Subtype.val h)
    have hnne' : (⟨n, hnUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) ≠ 1 := fun h => hnne (congrArg Subtype.val h)
    have hconj_eq : (⟨w, hwUW1⟩ : ↥(hyp.U ⊔ hyp.W1)) * ⟨n, hnUW1⟩ * ⟨w, hwUW1⟩⁻¹ = ⟨n, hnUW1⟩ :=
      Subtype.ext (by simpa using hcomm)
    exact bdata.UW1_frobenius.conj_frobenius _ hwmem hwne' _ hnmem hnne' hconj_eq

/-- **`S`-side dual of `tConjugate_fitting_data`** (Pf (13.17.a), V-side L~S exclusion input): for a
maximal `L` conjugate to `S`, the Fitting kernel `L_F` is a `p`-group of order `p^q` containing `W₂`
and meeting `V` trivially.  **Now proven** (the V-side mirror of `tConjugate_fitting_data`): part (1)
`|L_F| = p^q` from the proven `card_P_eq` via the `S`-conjugation equivariance of `M_F`; part (2)
`W₂ ≤ L_F` places the `p`-group `W₂ ⊆ N_G(V) ⊆ L` in the normal `p`-Hall `L_F`; part (3) `L_F ⊓ V = ⊥`
from `|L_F| = p^q` coprime to `|V|` (`V ⋊ W₂` Frobenius, `(|V|, p) = 1`).  `IsTypeII T` (for the
`V ⋊ W₂` Frobenius) is threaded from `exists_typeI_maximal_overNormalizer_V`. -/
theorem sConjugate_fitting_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    {L : Subgroup G} {g : G} (hconj : MulAut.conj g • L = hyp.S)
    (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.p ^ hyp.q ∧
      hyp.W2 ≤ maxNilpotentNormalHall L ∧
      maxNilpotentNormalHall L ⊓ hyp.V = ⊥ := by
  -- part 1: `|L_F| = p^q` (`card_P_eq`, proven, via the `S`-conjugation equivariance of `M_F`).
  have hLFcard : Nat.card ↥(maxNilpotentNormalHall L) = hyp.p ^ hyp.q := by
    have hMF : MulAut.conj g • maxNilpotentNormalHall L = hyp.P := by
      rw [maxNilpotentNormalHall_pointwise_smul, hconj, ← hyp.P_eq_SF]
    have hcard : Nat.card ↥(maxNilpotentNormalHall L) = Nat.card ↥hyp.P := by
      rw [← hMF]
      exact Nat.card_congr
        (Subgroup.equivSMul (MulAut.conj g) (maxNilpotentNormalHall L)).toEquiv
    rw [hcard]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  -- `W₂ ⊆ N_G(V) ⊆ L`.
  have hW2leL : hyp.W2 ≤ L := hyp.W2_normalizes_V.trans hNVL
  -- part 2: `W₂ ≤ L_F` — `W₂` a `p`-group in `L`, `L_F` the normal `p`-Hall subgroup.
  have hW2leLF : hyp.W2 ≤ maxNilpotentNormalHall L := by
    refine pgroup_le_of_normal_coprime_index (S := L) hyp.p_prime hW2leL
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L) ?_ ?_ ?_
    · have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall L
      have hcard_eq : Nat.card ↥((maxNilpotentNormalHall L).subgroupOf L)
          = Nat.card ↥(maxNilpotentNormalHall L) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L)).toEquiv
      exact hcard_eq ▸ Ch03.IsHallSubgroup.coprime_index hHall
    · rw [hLFcard]; exact dvd_pow_self hyp.p hyp.q_prime.pos.ne'
    · intro w hw
      have heq : orderOf (⟨w, hw⟩ : ↥hyp.W2) = orderOf w :=
        (orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨w, hw⟩).symm
      have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W2) ∣ Nat.card ↥hyp.W2 := orderOf_dvd_natCard _
      rw [heq, ← hyp.p_eq_card_W2] at h1
      exact h1
  -- part 3: `L_F ⊓ V = ⊥` — `|L_F| = p^q` coprime to `|V|` (`V ⋊ W₂` Frobenius gives `(|V|, p) = 1`).
  have hLFV : maxNilpotentNormalHall L ⊓ hyp.V = ⊥ := by
    obtain ⟨tpd, htpdV, htpdW1, _⟩ := reconciled_typePData_T hG hyp
    obtain ⟨tdata⟩ := hTTypeII
    have htpdVne : tpd.U ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
        rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
      rw [hbot, Subgroup.card_bot] at h1
      exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
    have hVW2frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
        ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
          (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
      have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
      rwa [htpdV, htpdW1] at h
    have hcopVp : Nat.Coprime (Nat.card ↥hyp.V) hyp.p := by
      have hk := hVW2frob.coprime_card_kernel_complement
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
        ← hyp.p_eq_card_W2] at hk
      exact hk
    have hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (Nat.card ↥hyp.V) := by
      rw [hLFcard]; exact hcopVp.symm.pow_left hyp.q
    exact Subgroup.inf_eq_bot_of_coprime hcop
  exact ⟨hLFcard, hW2leLF, hLFV⟩

/-- **`T`-side dual of `exists_typeI_maximal_overNormalizer_U`** (Pf (13.17.a/b), V-side): for `T`
type II, a maximal subgroup `L` over `N_G(V)` is type I with `V ⊆ L_F`.  Mirror of the `U`-side with
the two exclusion branches swapped: `L ~ T` is ruled out by the Hall conjugacy `N_G(V) ⊄ T`
(`not_normalizer_V_le_T`), and `L ~ S` by the `|L_F| = p^q` order contradiction
(`sConjugate_fitting_data`) against the `V W₂` Frobenius (from the reconciled `TypePData T`). -/
theorem exists_typeI_maximal_overNormalizer_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) :
    ∃ L : Subgroup G, L ∈ maximalSubgroups G ∧ IsTypeI L ∧
      Subgroup.normalizer (hyp.V : Set G) ≤ L ∧ hyp.V ≤ maxNilpotentNormalHall L := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW2, _⟩ := reconciled_typePData_T _hG hyp
  have hdisj : hyp.Q ⊓ hyp.V = ⊥ := hyp.Q_inf_V_eq_bot
  have hcop : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.Q) :=
    coprime_card_V_card_Q_of_disjoint hyp tdata hdisj
  have hNVT : ¬ Subgroup.normalizer (hyp.V : Set G) ≤ hyp.T :=
    not_normalizer_V_le_T _hG hyp tdata (exists_conj_typeP_V_of_coprime _hG hyp tdata hcop)
  have hVne : hyp.V ≠ ⊥ := by
    obtain ⟨x, _, hVconj⟩ := exists_conj_typeP_V_of_coprime _hG hyp tdata hcop
    rw [hVconj]
    exact mt (pointwise_smul_eq_bot_iff (MulAut.conj x)).mp tdata.common.1
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hVleT : hyp.V ≤ hyp.T := (le_sup_right.trans hyp.T_deriv_eq_QV.ge).trans hM'_le_T
  have hVneTop : hyp.V ≠ ⊤ := fun hVtop =>
    (mem_maximalSubgroups.mp hyp.T_maximal).1 (top_le_iff.mp (hVtop ▸ hVleT))
  have hNVtop : Subgroup.normalizer (hyp.V : Set G) ≠ ⊤ := by
    intro hNtop
    haveI hVnormal : (hyp.V).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases _hG.simple.eq_bot_or_eq_top_of_normal hyp.V hVnormal with h | h
    · exact hVne h
    · exact hVneTop h
  obtain ⟨L, hNVL, hLmaximal⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G => K ≠ ⊤) hNVtop
  have hLmem : L ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr ⟨hLmaximal.1, fun b hLb => by
      by_contra hbne
      exact lt_irrefl L (lt_of_lt_of_le hLb (hLmaximal.2 hbne hLb.le))⟩
  -- `V W₂` Frobenius from the reconciled `TypePData T` (used by both exclusion branches).
  have htpdVne : tpd.U ≠ ⊥ := by rw [htpdV]; exact hVne
  have hVW2frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
        (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
    rwa [htpdV, htpdW2] at h
  rcases hyp.theorem88_caseB L hLmem with hLI | hLconjS | hLconjT
  · exact ⟨L, hLmem, hLI, hNVL,
      typeI_overNormalizer_V_le_fitting _hG hyp ⟨tdata⟩ hLmem hLI hNVL⟩
  · -- `L ~ S` excluded (order contradiction, mirror of the S-side `L ~ T`).
    exfalso
    obtain ⟨g, hg⟩ := hLconjS
    obtain ⟨_hLFcard, hW2le, hLFV⟩ := sConjugate_fitting_data _hG hyp ⟨tdata⟩ hg hNVL
    have hVleL : hyp.V ≤ L := Subgroup.le_normalizer.trans hNVL
    have hV_norm_LF : hyp.V ≤ Subgroup.normalizer (maxNilpotentNormalHall L) :=
      hVleL.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L)
    have hVW2_le_V : ⁅hyp.V, hyp.W2⁆ ≤ hyp.V :=
      OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hyp.W2_normalizes_V
    have hVW2_le_LF : ⁅hyp.V, hyp.W2⁆ ≤ maxNilpotentNormalHall L := by
      refine (Subgroup.commutator_mono (le_refl hyp.V) hW2le).trans ?_
      rw [Subgroup.commutator_comm]
      exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hV_norm_LF
    have hVW2_bot : ⁅hyp.V, hyp.W2⁆ = ⊥ :=
      le_bot_iff.mp ((le_inf hVW2_le_LF hVW2_le_V).trans hLFV.le)
    have hVcent : hyp.V ≤ Subgroup.centralizer (hyp.W2 : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVW2_bot
    have hW2ne : hyp.W2 ≠ ⊥ := by
      intro hbot
      have : hyp.p = 1 := by rw [hyp.p_eq_card_W2, hbot, Subgroup.card_bot]
      exact hyp.p_prime.one_lt.ne' this
    obtain ⟨w, hwW2, hwne⟩ := (hyp.W2.bot_or_exists_ne_one).resolve_left hW2ne
    obtain ⟨n, hnV, hnne⟩ := (hyp.V.bot_or_exists_ne_one).resolve_left hVne
    have hcomm : w * n * w⁻¹ = n := by
      have := hVcent hnV w hwW2
      rw [mul_inv_eq_iff_eq_mul, this]
    have hwVW2 : w ∈ hyp.V ⊔ hyp.W2 := Subgroup.mem_sup_right hwW2
    have hnVW2 : n ∈ hyp.V ⊔ hyp.W2 := Subgroup.mem_sup_left hnV
    have hwmem : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ∈ hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2) := hwW2
    have hnmem : (⟨n, hnVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ∈ hyp.V.subgroupOf (hyp.V ⊔ hyp.W2) := hnV
    have hwne' : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ≠ 1 := fun h => hwne (congrArg Subtype.val h)
    have hnne' : (⟨n, hnVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ≠ 1 := fun h => hnne (congrArg Subtype.val h)
    have hconj_eq : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) * ⟨n, hnVW2⟩ * ⟨w, hwVW2⟩⁻¹ = ⟨n, hnVW2⟩ :=
      Subtype.ext (by simpa using hcomm)
    exact hVW2frob.conj_frobenius _ hwmem hwne' _ hnmem hnne' hconj_eq
  · -- `L ~ T` excluded (Hall conjugacy, mirror of the S-side `L ~ S`): `N_G(V) ⊆ T` vs `hNVT`.
    obtain ⟨g, hg⟩ := hLconjT
    have hVhall_cop : Nat.Coprime (Nat.card ↥hyp.V) ((hyp.V.subgroupOf hyp.T).index) := by
      have frobcop : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.W2) := by
        have h := hVW2frob.coprime_card_kernel_complement
        rwa [Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_left : hyp.V ≤ hyp.V ⊔ hyp.W2)).toEquiv,
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_right : hyp.W2 ≤ hyp.V ⊔ hyp.W2)).toEquiv] at h
      have hQleM' : hyp.Q ≤ derivedInG hyp.T := le_sup_left.trans hyp.T_deriv_eq_QV.ge
      have hidxM' : ((derivedInG hyp.T).subgroupOf hyp.T).index = Nat.card ↥hyp.W2 := by
        rw [← htpdW2, ← tpd.card_W1_eq_derived_index]
      have hidxQ : (hyp.Q.subgroupOf (derivedInG hyp.T)).index = Nat.card ↥hyp.V := by
        rw [hyp.Q_eq_TF, ← tpd.card_U_eq_index, htpdV]
      have hTcard : Nat.card ↥hyp.T
          = Nat.card ↥hyp.W2 * (Nat.card ↥hyp.V * Nat.card ↥hyp.Q) := by
        have e1 := ((derivedInG hyp.T).subgroupOf hyp.T).index_mul_card
        have e2 := (hyp.Q.subgroupOf (derivedInG hyp.T)).index_mul_card
        rw [hidxM', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'_le_T).toEquiv] at e1
        rw [hidxQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleM').toEquiv] at e2
        rw [← e1, ← e2]
      have hidxV := (hyp.V.subgroupOf hyp.T).index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleT).toEquiv] at hidxV
      have hidxVeq : (hyp.V.subgroupOf hyp.T).index = Nat.card ↥hyp.Q * Nat.card ↥hyp.W2 := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥hyp.V))
        rw [hidxV, hTcard]; ring
      rw [hidxVeq]
      exact hcop.mul_right frobcop
    exact absurd (normalizer_le_of_isHall_subgroupOf_of_conj
        (_hG.solvable_of_mem_maximalSubgroups hyp.T_maximal) hVleT
        (isHall_subgroupOf_primeFactors_of_coprime_index hVleT hVhall_cop) hg hNVL) hNVT

/-- **Peterfalvi (13.17.c), Huppert step.**  If `W₁` lies in a Frobenius complement `E` of the
type-I subgroup `L`, then `E ⊆ Q W₂`.

*Proof (Pf p.82):* `E` is a Frobenius complement of **odd** order (`E ≤ L ≤ G`, `|G|` odd), so by
Huppert ([H] Kapitel V Satz 8.18 b), `normal_of_card_prime_of_isFrobeniusGroup_of_odd`) its
prime-order subgroup `W₁` (`|W₁| = q`) is normal in `E`.  Hence `E ⊆ N_G(W₁) = C_G(W₁) = Q W₂`
by (13.16) (`normalizer_W1`).  This is the step of (13.17.c) consuming the new Frobenius-complement
structure theory; the remaining order analysis (`|E| ∈ {q, p q}`, cyclic Sylows by [BG] 3.9, and
the `(14.5)` exclusion of `E = W₁`) builds on this containment. -/
theorem complement_le_QW2 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T)
    {L : Subgroup G} (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ≤ hyp.Q ⊔ hyp.W2 := by
  set E := frob.complement with hEdef
  -- `W₁ ≤ L`, and `W₁` (as a subgroup of `↥L`) is contained in `E`.
  have hEleL : E.map L.subtype ≤ L := Subgroup.map_subtype_le E
  have hW1L : hyp.W1 ≤ L := hW1E.trans hEleL
  have hW1L_le_E : hyp.W1.subgroupOf L ≤ E := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨e, he, hee⟩ := hW1E hx
    have hex : e = x := Subtype.coe_injective (by simpa using hee)
    rw [← hex]; exact he
  -- `R := W₁` viewed inside `E`, of prime order `q`.
  set R : Subgroup ↥E := (hyp.W1.subgroupOf L).subgroupOf E with hRdef
  have hRcard : Nat.card ↥R = hyp.q := by
    rw [hRdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1L_le_E).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1L).toEquiv]
    exact hyp.q_eq_card_W1.symm
  -- `E` has odd order (it divides `|G|`).
  have hEdvd : Nat.card ↥E ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card E).trans (Subgroup.card_subgroup_dvd_card L)
  have hodd : Odd (Nat.card ↥E) := _hG.odd.of_dvd_nat hEdvd
  -- Huppert V.8.18 b): `W₁` is normal in `E`, so `E` normalizes `W₁` in `↥L`.
  haveI hRnormal : R.Normal :=
    OddOrder.Isaacs.Ch06.normal_of_card_prime_of_isFrobeniusGroup_of_odd
      frob.frobenius hodd hyp.q_prime hRcard
  have hEnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hW1L_le_E).mp hRnormal
  -- Lift to `G`: `E.map L.subtype ≤ N_G(W₁)`.
  have hEN : E.map L.subtype ≤ Subgroup.normalizer (hyp.W1 : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have heN := hEnorm he
    rw [Subgroup.mem_normalizer_iff] at heN ⊢
    intro w
    constructor
    · intro hw
      have hwL : w ∈ L := hW1L hw
      have hw' : (⟨w, hwL⟩ : ↥L) ∈ hyp.W1.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; exact hw
      have hconj := ((heN ⟨w, hwL⟩).mp hw')
      rw [Subgroup.mem_subgroupOf] at hconj
      simpa using hconj
    · intro hw
      -- the conjugate lies in `W₁ ≤ L`, so `w ∈ L`, and we apply `heN` backwards.
      have he' : (L.subtype e : G) ∈ L := e.2
      have hwL : w ∈ L := by
        have hrw : w = (L.subtype e)⁻¹ * ((L.subtype e) * w * (L.subtype e)⁻¹) * (L.subtype e) := by
          group
        rw [hrw]
        exact L.mul_mem (L.mul_mem (L.inv_mem he') (hW1L hw)) he'
      have hconjmem : (e * ⟨w, hwL⟩ * e⁻¹) ∈ hyp.W1.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; simpa using hw
      have hfin := (heN ⟨w, hwL⟩).mpr hconjmem
      rw [Subgroup.mem_subgroupOf] at hfin
      simpa using hfin
  -- (13.16): `N_G(W₁) = C_G(W₁) = Q W₂`.
  have h1316 := normalizer_W1 _hG hyp hTTypeII
  calc E.map L.subtype ≤ Subgroup.normalizer (hyp.W1 : Set G) := hEN
    _ = Subgroup.centralizer (hyp.W1 : Set G) := h1316.1
    _ = hyp.Q ⊔ hyp.W2 := h1316.2

/-- §13 structural data for the semidirect product `Q ⋊ W₂` (`Q = T_F`) consumed by the
`∃ y` step of (13.17.c).  `W₂` normalizes `Q` (as `W₂ ≤ T` and `Q ◁ T`), meets it trivially, and
`p ∤ |Q| = q^p` (since `p ≠ q`).

*Proof.*  `W₂ ≤ W = S ⊓ T ≤ T` and `Q = T_F ◁ T` (`maxNilpotentNormalHall_le_normalizer`) give the
normalization.  The distinctness `p ≠ q` is forced because otherwise `W₁` and `W₂` would be equal
order-`q` subgroups of the cyclic `W` (`eq_of_card_eq_prime_of_isCyclic`), contradicting
`W₁ ⊓ W₂ = 1`; then `p ∤ q^p`, and the coprimality `|Q| ⟂ |W₂| = p` gives `Q ⊓ W₂ = 1`.  The only
gated input is `|Q| = q^p` (`card_Q_eq`, the isolated §13 counting residual B1). -/
theorem Q_W2_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    hyp.W2 ≤ Subgroup.normalizer (hyp.Q : Set G) ∧ hyp.Q ⊓ hyp.W2 = ⊥ ∧
      ¬ hyp.p ∣ Nat.card ↥hyp.Q := by
  -- `W₂ ≤ W = S ⊓ T ≤ T`.
  have hW2T : hyp.W2 ≤ hyp.T :=
    (le_sup_right.trans hyp.W_eq_join.ge).trans (hyp.W_eq_inter.le.trans inf_le_right)
  -- Conjunct 1: `W₂ ≤ N_G(Q)`, as `Q = T_F ◁ T` and `W₂ ≤ T`.
  have hWnorm : hyp.W2 ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]
    exact hW2T.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T)
  -- `p ≠ q`: else `W₁` and `W₂` are equal order-`q` subgroups of the cyclic `W`.
  have hpq : hyp.p ≠ hyp.q := by
    intro heq
    haveI : IsCyclic ↥hyp.W := hyp.W_cyclic
    have hW1W : hyp.W1 ≤ hyp.W := le_sup_left.trans hyp.W_eq_join.ge
    have hW2W : hyp.W2 ≤ hyp.W := le_sup_right.trans hyp.W_eq_join.ge
    have hW1card : Nat.card ↥(hyp.W1.subgroupOf hyp.W) = hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1W).toEquiv]; exact hyp.q_eq_card_W1.symm
    have hW2card : Nat.card ↥(hyp.W2.subgroupOf hyp.W) = hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2W).toEquiv, ← heq]
      exact hyp.p_eq_card_W2.symm
    have hsubeq : hyp.W1.subgroupOf hyp.W = hyp.W2.subgroupOf hyp.W :=
      Ch06.eq_of_card_eq_prime_of_isCyclic hyp.q_prime hW1card hW2card
    have hWeq : hyp.W1 = hyp.W2 := by
      have hmap := congrArg (Subgroup.map hyp.W.subtype) hsubeq
      rwa [Subgroup.map_subgroupOf_eq_of_le hW1W, Subgroup.map_subgroupOf_eq_of_le hW2W] at hmap
    have hbot : hyp.W1 = ⊥ := by
      have h := hyp.W1_inf_W2_eq_bot; rwa [← hWeq, inf_idem] at h
    have hq1 : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hbot, Subgroup.card_bot]
    exact hyp.q_prime.one_lt.ne' hq1
  -- Conjunct 3: `p ∤ |Q| = q^p`, since `p ∤ q` (distinct primes).
  have hpQ : ¬ hyp.p ∣ Nat.card ↥hyp.Q := by
    rw [card_Q_eq hG hyp hTTypeII]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hyp.p_prime hyp.q_prime).mp
      (hyp.p_prime.dvd_of_dvd_pow hdvd))
  -- Conjunct 2: `Q ⊓ W₂ = ⊥`, from coprimality `|Q| ⟂ p = |W₂|`.
  refine ⟨hWnorm, ?_, hpQ⟩
  apply Subgroup.inf_eq_bot_of_coprime
  rw [← hyp.p_eq_card_W2]
  exact (hyp.p_prime.coprime_iff_not_dvd.mpr hpQ).symm

end OddOrder.Peterfalvi.S15
