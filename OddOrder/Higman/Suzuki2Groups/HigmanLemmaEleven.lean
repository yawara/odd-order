/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralSpectrum

/-!
# Higman's classification of Suzuki 2-groups of length two

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 11, pp. 88--89.

The proof keeps the two finite-field degrees separate until Higman's trace
argument rules out a proper odd extension.  This leaf contains the common
splitting-field eigenbasis, unequal-degree bracket normal form, square trace
formula, and the final comparison with the concrete type-A extension.
-/

set_option autoImplicit false

open Module Polynomial
open OddOrder.RepresentationTheory
open scoped TensorProduct

namespace OddOrder.Higman.Suzuki2Groups

universe uCommonField

/-! ## The second-layer Singer basis in a common splitting field -/

/-- Singer--Frobenius coordinates transported to a chosen finite splitting
field containing the canonical Singer field.  Faithfulness of the original
action is not assumed: it is recovered on the effective image. -/
theorem exists_singerFrobeniusEigenbasis_of_transitive_generator_over
    {C V L : Type uCommonField} [CommGroup C] [IsCyclic C] [Finite C]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Field L] [Finite L] [Algebra (ZMod 2) L]
    (rho : Representation (ZMod 2) C V) (n : ℕ) (hn : 2 ≤ n)
    (hfin : Module.finrank (ZMod 2) V = n)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ c : C, rho c v = w)
    (c : C) (hcgen : ∀ x : C, x ∈ Subgroup.zpowers c)
    (iota : GaloisField 2 n →ₐ[ZMod 2] L) :
    ∃ (e : V ≃ₗ[ZMod 2] GaloisField 2 n) (nu : GaloisField 2 n)
      (b : Basis (Fin n) L (L ⊗[ZMod 2] V)),
      IsPrimitiveRoot nu (2 ^ n - 1) ∧
      e.conj (rho c) = Algebra.lmul (ZMod 2) (GaloisField 2 n) nu ∧
      Algebra.adjoin (ZMod 2) ({nu} : Set (GaloisField 2 n)) = ⊤ ∧
      IsPrimitiveRoot (iota nu) (2 ^ n - 1) ∧
      ∀ s, (rho c).baseChange L (b s) =
        (iota nu) ^ (2 ^ s.val) • b s := by
  obtain ⟨e, nu, _bK, hprim, hconj, hgen, _hbK⟩ :=
    exists_singerFrobeniusEigenbasis_of_transitive_generator
      rho n hn hfin htrans c hcgen
  have hcharK : (rho c).charpoly = minpoly (ZMod 2) nu :=
    charpoly_eq_minpoly_of_conj_lmul (rho c) e nu hconj hgen
  have hcharL : (rho c).charpoly = minpoly (ZMod 2) (iota nu) := by
    calc
      (rho c).charpoly = minpoly (ZMod 2) nu := hcharK
      _ = minpoly (ZMod 2) (iota nu) :=
        (minpoly.algHom_eq iota iota.injective nu).symm
  have hprimL : IsPrimitiveRoot (iota nu) (2 ^ n - 1) :=
    hprim.map_of_injective iota.injective
  obtain ⟨b, hb⟩ := exists_frobeniusEigenbasis_of_charpoly_eq_minpoly
    (rho c) n hn (iota nu) hfin hcharL hprimL
  exact ⟨e, nu, b, hprim, hconj, hgen, hprimL, hb⟩

end OddOrder.Higman.Suzuki2Groups
