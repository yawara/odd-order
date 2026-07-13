import OddOrder.FeitThompsonSetup
import OddOrder.Peterfalvi.S13_TypeDetermination

/-!
# FeitThompsonPairProducer

The §16 maximal-pair producer `section16MaximalPair_of_isMinimalSimpleOdd`, extracted from
`S13_TypeDetermination` to a leaf **downstream** of `FeitThompsonSetup`.  The producer discharges
the (12.17) `theorem88_caseB_holds` obligation via `exists_section16MaximalPair_data` (defined in
`FeitThompsonSetup`, which pulls the `AppC` capstone); keeping it out of `S13_TypeDetermination`
lets the §11–§13 type-determination stay **upstream** of the capstone — the §12–16 import inversion
fix (HUB RULING, issue 9093).  Only `FeitThompson` consumes this.
-/

namespace OddOrder

open OddOrder.BG
open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

/-- **BG §16 maximal-pair producer** — *lane-g* (BG §16 main results).
Constructs the maximal pair `S, T`, their type classification, and the case-(b)
trichotomy of (8.8) from a minimal simple group of odd order.

This is the first real consumer of the §16 main results.  Peterfalvi (8.8)
(`maximalSubgroup_type_dichotomy`, repackaging BG Theorem I) gives the dichotomy
"every maximal subgroup is Type I, or the type-P pair `S, T` covers everything".
The second branch supplies every field directly.  The first branch is impossible:
Peterfalvi (12.17) (`theorem88_caseB_holds`, the all-Type-I non-existence argument
of §7.11/§12) produces a *non-Type-I* maximal subgroup, which contradicts "every
maximal subgroup is Type I" via the type-exclusivity corollary of Proposition 16.1
(`not_isTypeI_of_isTypeNonI`). -/
noncomputable def section16MaximalPair_of_isMinimalSimpleOdd {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) : Section16MaximalPair G := by
  classical
  -- `exists_section16MaximalPair_data` supplies the canonical pair `S, T = Mstar` with the full
  -- κ-Hall witness data.  The four subgroup witnesses are extracted by choice (the `Exists` cannot
  -- be `rcases`'d into the `Type`-valued structure goal); the structural conjunction is an `And`
  -- (large-eliminating), so it `obtain`s into named hypotheses directly.
  have e := exists_section16MaximalPair_data hG
    (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG)
  obtain ⟨hSmax, hTmax, hSneT, hSnonI, hTnonI, hone, hcaseB, hKleS, hKhall, hKstareq,
    hStypeP, hTtypeP, hSTnconj, hKstarleT, hKstarhall, hKeq, hZcyc, hKlt⟩ :=
    e.choose_spec.choose_spec.choose_spec.choose_spec
  exact
    { S := e.choose
      T := e.choose_spec.choose
      K := e.choose_spec.choose_spec.choose
      Kstar := e.choose_spec.choose_spec.choose_spec.choose
      S_maximal := hSmax
      T_maximal := hTmax
      S_ne_T := hSneT
      S_nonI := hSnonI
      T_nonI := hTnonI
      one_typeII := hone
      theorem88_caseB := hcaseB
      K_le_S := hKleS
      K_hall := hKhall
      Kstar_eq := hKstareq
      S_typeP := hStypeP
      T_typeP := hTtypeP
      S_T_not_conj := hSTnconj
      Kstar_le_T := hKstarleT
      Kstar_hall := hKstarhall
      K_eq := hKeq
      Z_cyclic := hZcyc
      K_lt_Kstar := hKlt
      S_typeP2 := isTypeP2_of_typeP_kappaHall_lt hG hSmax hStypeP hKleS hKhall hKstareq hKlt }

end OddOrder
