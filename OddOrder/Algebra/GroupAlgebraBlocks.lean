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
* `OddOrder.GroupAlgebra.exists_modularDatum` — the splitting datum the modular theory carries,
  for *any* finite group, over an algebraically closed field
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
  obtain ⟨n, d, hd, π, hπ, -, hker⟩ := exists_algHom_pi_matrix_of_isAlgClosed k (MonoidAlgebra k G)
  have : ∀ i, NeZero (d i) := hd
  have : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨0⟩
  set π' : MonoidAlgebra k G →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k := π.toRingHom with hπ'def
  have hlin : ∀ (c : k) (a : MonoidAlgebra k G), π' (c • a) = c • π' a := fun c a => map_smul π c a
  have : Finite (Block π' hπ hlin) := Quotient.finite _
  have : Fintype (Block π' hπ hlin) := Fintype.ofFinite _
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

/-- **The modular datum of `k[G]`, for any finite `G` over an algebraically closed `k`.**

The chain of `Modular/` carries the splitting of `k[G]` as five separate hypotheses — the map `π`
onto a product of matrix algebras, its surjectivity, its `k`-linearity, the identification of its
kernel with `J(k[G])`, and nilpotence of the elements the block character kills.  All five come
from `exists_algHom_pi_matrix_of_isAlgClosed` as soon as `k` is algebraically closed, with no
condition on `G`.

This is what makes the per-element data of Navarro (5.11) affordable: that result needs the datum
of `C_G(x)` for each `x`, and over `𝔽̄_p` — the residue field of `𝓞_ℂ_[p]` — every centraliser
supplies one. -/
theorem exists_modularDatum (k : Type*) [Field k] [IsAlgClosed k] (G : Type*) [Group G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (nn : ι → Type) (_ : ∀ i, Fintype (nn i))
      (_ : ∀ i, DecidableEq (nn i)) (_ : ∀ i, Nonempty (nn i))
      (π : MonoidAlgebra k G →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π)
      (hlin : ∀ (c : k) (a : MonoidAlgebra k G), π (c • a) = c • π a),
      RingHom.ker π = Ring.jacobson (MonoidAlgebra k G) ∧
        ∀ z : Subalgebra.center k (MonoidAlgebra k G),
          blockCharacterPi π hπ hlin z = 0 → IsNilpotent z := by
  classical
  obtain ⟨n, d, hd, π, hπ, hkerJ, hker⟩ :=
    exists_algHom_pi_matrix_of_isAlgClosed k (MonoidAlgebra k G)
  have : ∀ i, NeZero (d i) := hd
  have : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨0⟩
  set π' : MonoidAlgebra k G →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k := π.toRingHom with hπ'def
  have hlin : ∀ (c : k) (a : MonoidAlgebra k G), π' (c • a) = c • π' a := fun c a => map_smul π c a
  refine ⟨Fin n, inferInstance, fun i => Fin (d i), inferInstance, inferInstance, inferInstance,
    π', hπ, hlin, hkerJ, fun z hz => ?_⟩
  obtain ⟨m, hm⟩ := hker _ (RingHom.mem_ker.mpr ((blockCharacterPi_eq_zero_iff π' hπ hlin).mp hz))
  exact ⟨m, Subtype.ext (by simpa using hm)⟩

/-- **The nil-kernel hypothesis is implied by `ker π = J(A)`.**

`A` is Artinian (finite-dimensional over a field), so its Jacobson radical is nilpotent
(`IsSemiprimaryRing.isNilpotent`); a central element killed by every block character lies in
`ker π = J(A)` (`blockCharacterPi_eq_zero_iff`), hence is nilpotent.

This is what makes the hypothesis available for *derived* splittings — notably
`quotientPi`, whose kernel is the Jacobson radical of the quotient group algebra
(`ker_quotientPi`) but which is not produced by `exists_modularDatum`. -/
theorem isNilpotent_of_blockCharacterPi_eq_zero {k : Type*} [Field k]
    {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
    [∀ i, Nonempty (nn i)]
    {A : Type*} [Ring A] [Algebra k A] [Module.Finite k A]
    (π : A →+* ∀ j, Matrix (nn j) (nn j) k) (hπ : Function.Surjective π)
    (hlin : ∀ (c : k) (a : A), π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson A)
    (z : Subalgebra.center k A) (hz : MatrixModule.blockCharacterPi π hπ hlin z = 0) :
    IsNilpotent z := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨m, hm⟩ : IsNilpotent (Ring.jacobson A) := IsSemiprimaryRing.isNilpotent
  have hmem : (z : A) ∈ Ring.jacobson A := by
    rw [← hkerJ]
    exact RingHom.mem_ker.mpr ((MatrixModule.blockCharacterPi_eq_zero_iff π hπ hlin).mp hz)
  refine ⟨m, Subtype.ext ?_⟩
  have hpow := Ideal.pow_mem_pow hmem m
  rw [hm] at hpow
  simpa using hpow

end OddOrder.GroupAlgebra
