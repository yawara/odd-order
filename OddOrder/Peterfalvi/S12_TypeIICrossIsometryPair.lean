/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_TypeIIGridTranspose

/-!
# Peterfalvi (10.7): the cross-isometry package at the canonical pair

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §10
(10.7); Coq mirror `PFsection10.v` (`Frob_der1_type2`).

The pair-witness production of the (10.7) cross-isometry package
(`TypeIICrossIsometryData`): at the `M`-seeded canonical pair (`T = M`,
`Kstar = hyp.typeP.W1`, `exists_section16MaximalPair_around`), with the §9 setup of the
type-II member `mp.S` wired to the pair (`exists_typesIIIIIIVSetup_Sdata`), the
character-theoretic fields are **produced**, not posited:

* `tau2` — the (5.7) coherent extension, `typeII_T2_coherent`'s `IsCoherent.extension`;
* `r'`, `delta'`, `nu_tau2_eq` — the (5.8) row pin
  `Hypothesis.exists_nu_extension_eq_alignedRow_at_pair` (the assembled grid transpose of
  issue 9079: (9.8) classification → (5.8) dichotomy → pair transpose → fiber sweep).

The remaining four fields (`lam_ortho_grid`, `zeta_ortho_grid`, `zeta_lam_ortho`,
`cross_zero`) are the **(5.3.b) / (8.18.b) support-geometry obligations** (obligation 3 of
the (10.7) frontier note `notes/peterfalvi/s10_7_derived_frobenius.md`) — they are `sorry`d
here as the explicit remaining work, so this file is the single discharge point for the
gate's residual.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory
open OddOrder.GroupTheory

variable {G : Type*} [Group G]

set_option linter.unusedVariables false in
open scoped Classical FiniteInduce in
/-- **The (10.7) cross-isometry package at the canonical pair** (Coq `Frob_der1_type2`,
production step): for the `M`-seeded pair (`T = M`, `Kstar = hyp.typeP.W1`) and a
`(K, K*)`-reconciled §9 setup on the type-II member `mp.S`, the package exists with the
grid fields **honestly produced**: `tau2` is the (5.7) `T2`-coherent extension
(`typeII_T2_coherent`), and `nu_tau2_eq` is the (5.8) row pin
(`exists_nu_extension_eq_alignedRow_at_pair`).

The four support-geometry fields ((5.3.b) grid orthogonality and the (8.18.b)
cross-support vanishing) are the remaining obligation-3 content — `sorry`d here as the
explicit frontier (see the module docstring). -/
theorem exists_typeIICrossIsometryData_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {mp : Section16MaximalPair G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥mp.S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_red : ¬ IsIrreducibleCharacter nu)
    (hdeg : lam 1 = nu 1) :
    Nonempty (TypeIICrossIsometryData hG coh lam nu) := by
  classical
  -- the (5.7) `T2`-coherence on `mp.S`
  obtain ⟨c⟩ := typeII_T2_coherent hG mp.S_maximal (section16_S_isTypeII hG mp) data
    hlam_mem hlam_irr hnu_mem hnu_red hdeg
  -- the (5.8) row pin (the assembled grid transpose)
  obtain ⟨r', delta', hpm, hrow⟩ := hyp.exists_nu_extension_eq_alignedRow_at_pair hG
    hT hKstar hSW1 hSW2 hlam_mem hlam_irr hnu_mem hnu_red hdeg c
  exact ⟨{ tau2 := c.extension
           r' := r'
           delta' := delta'
           delta'_pm := hpm
           nu_tau2_eq := hrow
           lam_ortho_grid := sorry
           zeta_ortho_grid := sorry
           zeta_lam_ortho := sorry
           cross_zero := sorry }⟩

end OddOrder.Peterfalvi.S12
