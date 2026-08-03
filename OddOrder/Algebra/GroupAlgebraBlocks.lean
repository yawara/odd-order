/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AlgClosedSplitting
import OddOrder.Algebra.BlockIdempotent
import OddOrder.Algebra.GroupAlgebraDefectGroup

/-!
# The blocks of `k[G]` over an algebraically closed field

Everything the block machinery needs is available for `A = k[G]` once `k` is algebraically
closed, so the theory becomes unconditional:

* `exists_algHom_pi_matrix_of_isAlgClosed` supplies the splitting `π : k[G] →ₐ[k] ∏_i M_{d_i}(k)`
  with nil kernel — `k[G]` is finite dimensional, hence Artinian, so `J(k[G])` is nilpotent and
  `k[G] / J(k[G])` is split semisimple;
* `exists_completeOrthogonalIdempotents_block` then produces the block idempotents `e_B`, which
  are central, nonzero and primitive (`BlockIdempotent`);
* `GroupAlgebra.exists_conj_eq_of_isDefectGroup` applies to each of them.

The result is Brauer's theorem with no hypotheses beyond "`k` algebraically closed, `G` finite":
`1` splits into block idempotents, and the defect groups of each block form a single
`G`-conjugacy class.  Note that `k = 𝔽̄_p` really occurs in the intended application — it is the
residue field of the `p`-modular system `𝕎(𝔽̄_p)`.

## Main results

* `OddOrder.GroupAlgebra.exists_blockIdempotents_defectGroups_conj`
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra OddOrder.GAlgebra OddOrder.MatrixModule

open scoped OddOrder.Conjugation Pointwise

/-- **The block decomposition of `k[G]` and Brauer's theorem on defect groups**, over an
algebraically closed field and with no further hypotheses.

There is a finite family of idempotents summing to `1` and pairwise orthogonal — the block
idempotents — each central (so `G`-fixed under conjugation) and nonzero, and the defect groups of
each of them form a single `G`-conjugacy class. -/
theorem exists_blockIdempotents_defectGroups_conj (k : Type*) [Field k] [IsAlgClosed k]
    (G : Type*) [Group G] [Finite G] :
    ∃ (β : Type) (_ : Fintype β) (e : β → MonoidAlgebra k G),
      CompleteOrthogonalIdempotents e ∧
      (∀ c, ∀ g : G, g • e c = e c) ∧
      (∀ c, e c ≠ 0) ∧
      ∀ c (D D' : Subgroup G), IsDefectGroup (e c) D → IsDefectGroup (e c) D' →
        ∃ g : G, D = MulAut.conj g • D' := by
  classical
  obtain ⟨n, d, hd, π, hπ, hker⟩ := exists_algHom_pi_matrix_of_isAlgClosed k (MonoidAlgebra k G)
  haveI : ∀ i, NeZero (d i) := hd
  haveI : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨0⟩
  set π' : MonoidAlgebra k G →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k := π.toRingHom with hπ'def
  have hlin : ∀ (c : k) (a : MonoidAlgebra k G), π' (c • a) = c • π' a := fun c a => map_smul π c a
  haveI : Finite (Block π' hπ hlin) := Quotient.finite _
  haveI : Fintype (Block π' hπ hlin) := Fintype.ofFinite _
  -- The nil-kernel hypothesis of the block theory, from nilness of `ker π`.
  have hnil : ∀ x : Subalgebra.center k (MonoidAlgebra k G),
      blockCharacterPi π' hπ hlin x = 0 → IsNilpotent x := by
    intro x hx
    have hx0 := (blockCharacterPi_eq_zero_iff π' hπ hlin).mp hx
    obtain ⟨m, hm⟩ := hker _ (RingHom.mem_ker.mpr hx0)
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  obtain ⟨e, he, hfe⟩ := exists_completeOrthogonalIdempotents_block π' hπ hlin hnil
  refine ⟨Block π' hπ hlin, inferInstance, fun c => (e c : MonoidAlgebra k G),
    completeOrthogonalIdempotents_val π' hπ hlin he,
    fun c g => mem_center_iff_forall_smul_eq.mp (e c).2 g,
    fun c h0 => blockIdempotent_ne_zero π' hπ hlin (hfe c) (Subtype.ext h0), ?_⟩
  intro c D D' hD hD'
  refine exists_conj_eq_of_isDefectGroup (fun g => mem_center_iff_forall_smul_eq.mp (e c).2 g)
    (Subtype.ext_iff.mp (he.idem c))
    (fun h0 => blockIdempotent_ne_zero π' hπ hlin (hfe c) (Subtype.ext h0))
    (fun u hufix huidem hbu => ?_) hD hD'
  rcases eq_zero_or_eq_of_mul_eq_of_isIdempotentElem π' hπ hlin hnil (he.idem c) (hfe c)
    (u := ⟨u, mem_center_iff_forall_smul_eq.mpr hufix⟩) (Subtype.ext huidem)
    (Subtype.ext hbu) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

end OddOrder.GroupAlgebra
