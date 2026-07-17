/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_CertificateDischarge

/-!
# Peterfalvi (7.6) for a Frobenius family — the induced-family coherent datum

Downstream of `S09_CertificateDischarge` (`hypothesis76OfDade` discharges the (7.7.a)
`Hypothesis76.chiRho_decomp` certificate): each `FrobeniusFamily` member `i` yields the (7.6) datum
`Hypothesis76 G (H_i^#) (L_i)` with **no certificate assumed** — the coherence layer of
`card_G0_lower_bound` (issue 0044).
-/

namespace OddOrder.Peterfalvi.S09

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The Peterfalvi (7.6) coherent datum for the `i`-th family member.**  From the (7.1) datum
`hypothesis71 i` (Dade isometry via `isDadeIsometry_of_isDadeMap`) and the kernel `H_i ⊴ L_i`,
`hypothesis76OfDade` builds the induced family `{Ind_{H_i}^{L_i} θ}` and discharges the (7.7.a)
`chiRho_decomp` certificate. -/
noncomputable def hypothesis76 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k)
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)] :
    Hypothesis76 G (OddOrder.Peterfalvi.S04.sharp (F.H i : Set G)) (F.L i) :=
  Cert.hypothesis76OfDade (F.hypothesis71 i)
    (OddOrder.Peterfalvi.S04.isDadeIsometry_of_isDadeMap (F.hypothesis71 i).hyp
      (F.hypothesis71 i).τ (F.hypothesis71 i).isDadeMap (F.hypothesis71 i).hConjInvariant)
    (F.H i) (F.kernel_le i)
    (fun l _h hh => (F.mem_kernel_conj_iff_of_mem_L i l.2).mpr hh) rfl

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
