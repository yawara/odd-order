/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.EigenCornerInverse
import OddOrder.Algebra.EigenTraceVanishing
import OddOrder.Algebra.GroupAlgebraIdeal
import OddOrder.Algebra.SubgroupTruncation
import OddOrder.GroupTheory.RepresentationTheory.Modular.TwistedLayerSum

/-!
# Navarro (5.7): `χ(f_b h) = 0`

The five pieces are in place:

1. `exists_inducedBlock_witness` — (5.6): a `w ∈ 𝒪G` with `(1 - f_B) f_b = (1 - f_B) w`,
   `w f_b = w`, `H` centralising `w`, and `supp w ⊆ G ∖ H`;
2. `conjLayer` — the `p` cyclically permuted layers of `w`;
3. `exists_conj_eigen_corner` — the eigenvector `s` with `s^h = ζ s`, `f_b s f_b = s`, `s* = w*`;
4. `exists_corner_inverse_eigen` + `eq_zero_of_apply_eq_zero_of_corner_inverse` — `s` acts
   injectively on the part of the module fixed by `f_b`;
5. `trace_idempotent_mul_eq_zero` — hence the trace of `f_b h` vanishes.

This file wires them together for a representation `ρ : 𝒪G →+* End K M`.  The hypotheses on `w`
are exactly the four conclusions of (5.6), so the last step towards (5.2) is to feed
`exists_inducedBlock_witness` in; and `ρ f_B = 0` is (3.13.a) for `χ ∉ B`
(`apply_eq_zero_of_reduce_centralScalar_eq_zero`).

## Main results

* `OddOrder.RepresentationTheory.Modular.trace_blockIdempotent_mul_eq_zero` — Navarro (5.7)
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra OddOrder.GroupTheory
open OddOrder.GroupAlgebra (inclusionHom)

open scoped OddOrder.Conjugation

variable {𝒪 K F G M : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [Field K] [Algebra 𝒪 K]
  [CommRing F] [Group G] [Fintype G] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

omit [IsLocalRing 𝒪] [Fintype G] in
set_option linter.unusedFintypeInType false in
/-- If every element of `H` commutes with `w`, so does everything coming from `𝒪H`. -/
theorem commute_inclusionHom_of_forall_single {H : Subgroup G} {w : MonoidAlgebra 𝒪 G}
    (hw : ∀ u : ↥H, single (u : G) (1 : 𝒪) * w = w * single (u : G) 1)
    (a : MonoidAlgebra 𝒪 ↥H) : inclusionHom H a * w = w * inclusionHom H a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, zero_mul, mul_zero]
  | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]
  | single u r =>
    rw [OddOrder.GroupAlgebra.inclusionHom_single,
      show (single (u : G) r : MonoidAlgebra 𝒪 G) = r • single (u : G) 1 from by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one],
      smul_mul_assoc, mul_smul_comm, hw u]

-- The finiteness of `G` and `H` is consumed by the layer decomposition and the corner inverse.
set_option linter.unusedFintypeInType false in
/-- **Navarro (5.7).**  Let `f_b` be a block idempotent of `𝒪H`, `f_B` a central idempotent of
`𝒪G`, and `w` a witness as produced by (5.6).  If `h ∈ H` has `C_G(h_p) ≤ H`, and the module `M`
is annihilated by `f_B` — which is (3.13.a) for `χ ∉ B` — then the trace of `f_b h` on `M`
vanishes.

The root of unity `ζ` is asked to be a `p`-th root whose residue is `1` (automatic in
characteristic `p`, `eq_one_of_pow_eq_one_expChar`) and whose image in `K` is not `1`. -/
theorem trace_blockIdempotent_mul_eq_zero {p : ℕ} (hp : p.Prime) (H : Subgroup G) [Fintype ↥H]
    (φ : 𝒪 →+* F) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal 𝒪)
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hφζ : φ ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    {fb : MonoidAlgebra 𝒪 ↥H} (hfb : fb * fb = fb)
    (hfbc : ∀ u : ↥H, single (u : ↥H) (1 : 𝒪) * fb = fb * single (u : ↥H) 1)
    {fB : MonoidAlgebra 𝒪 G} (hfB : fB * fB = fB) (hfBc : ∀ a, Commute fB a)
    {w : MonoidAlgebra 𝒪 G}
    (hwa : (1 - fB) * inclusionHom H fb = (1 - fB) * w)
    (hwb : w * inclusionHom H fb = w)
    (hwc : ∀ u : ↥H, single (u : G) (1 : 𝒪) * w = w * single (u : G) 1)
    (hwd : ∀ g ∈ H, w.coeff g = 0)
    {h : ↥H} (hCH : Subgroup.centralizer {(pPart p (h : G))} ≤ H)
    (ρ : MonoidAlgebra 𝒪 G →+* Module.End K M)
    (hρ : ∀ (r : 𝒪) (x : MonoidAlgebra 𝒪 G), ρ (r • x) = algebraMap 𝒪 K r • ρ x)
    (hρB : ρ fB = 0) :
    LinearMap.trace K M (ρ (inclusionHom H fb) * ρ (single (h : G) (1 : 𝒪))) = 0 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set e : MonoidAlgebra 𝒪 G := inclusionHom H fb with hedef
  have he : e * e = e := by rw [hedef, ← map_mul, hfb]
  -- `H` centralises `e`, in particular `h` does
  have hcomme : ∀ u : ↥H, single (u : G) (1 : 𝒪) * e = e * single (u : G) 1 := by
    intro u
    rw [hedef, ← OddOrder.GroupAlgebra.inclusionHom_single (R := 𝒪) u 1, ← map_mul, ← map_mul,
      hfbc u]
  have hehsmul : (h : G) • e = e :=
    (OddOrder.GroupAlgebra.smul_eq_self_iff_commute (h : G) e).mpr (hcomme h)
  have hwhsmul : (h : G) • w = w :=
    (OddOrder.GroupAlgebra.smul_eq_self_iff_commute (h : G) w).mpr (hwc h)
  -- `e` commutes with `w`, so `w` is its own `e`-corner
  have hcommew : e * w = w * e := commute_inclusionHom_of_forall_single hwc fb
  have hew : e * w * e = w := by rw [mul_assoc, hwb, hcommew, hwb]
  -- the support of `w` misses `C_G(h_p)`
  have hsupp : ∀ x : G, w.coeff x ≠ 0 → ¬ Commute (pPart p (h : G)) x := by
    intro x hx hcon
    exact hx (hwd x (hCH (Subgroup.mem_centralizer_iff.mpr (by
      rintro y rfl; exact hcon))))
  have hhfin : IsOfFinOrder (h : G) := isOfFinOrder_of_finite _
  -- (5.7)'s eigenvector
  obtain ⟨s, hs1, hs2, hs3⟩ :=
    exists_conj_eigen_corner (R := 𝒪) (G := G) hp hζ hhfin he hehsmul hwhsmul hew hsupp φ hφζ
  -- `s ≡ w` modulo `𝔪`
  have hsw : s - w ∈ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 (MonoidAlgebra 𝒪 G)) := by
    refine (OddOrder.GroupAlgebra.mem_groupAlgebraIdeal_iff_mapRingHom_eq_zero
      (IsLocalRing.maximalIdeal 𝒪) φ hker _).mpr ?_
    rw [map_sub, hs3, sub_self]
  -- the corner inverse
  obtain ⟨y, hy, -⟩ := exists_corner_inverse_eigen (𝒪 := 𝒪) hfB hfBc he hwa hsw hs2
  -- the three endomorphisms
  have hes : e * s = s := by
    have h1 : e * s = e * (e * s * e) := by rw [hs2]
    rw [h1, ← mul_assoc, ← mul_assoc, he, hs2]
  have hse : s * e = s := by
    have h1 : s * e = (e * s * e) * e := by rw [hs2]
    rw [h1, mul_assoc, he, hs2]
  have hΦS : ρ (single (h : G) (1 : 𝒪)) * ρ s
      = algebraMap 𝒪 K ζ • (ρ s * ρ (single (h : G) (1 : 𝒪))) := by
    have hmul : single (h : G) (1 : 𝒪) * s = ζ • (s * single (h : G) 1) := by
      have hconj := hs1
      rw [OddOrder.GroupAlgebra.smul_eq_conj] at hconj
      have := congrArg (fun z : MonoidAlgebra 𝒪 G => z * single (h : G) (1 : 𝒪)) hconj
      simpa [mul_assoc, MonoidAlgebra.single_mul_single, smul_mul_assoc,
        ← MonoidAlgebra.one_def] using this
    rw [← map_mul, hmul, hρ, map_mul]
  refine trace_idempotent_mul_eq_zero hζK (S := ρ s) ?_ ?_ ?_ ?_ hΦS ?_
  · rw [← map_mul, he]
  · rw [← map_mul, ← map_mul, hcomme h]
  · rw [← map_mul, hes]
  · rw [← map_mul, hse]
  · intro v hv hsv
    exact eq_zero_of_apply_eq_zero_of_corner_inverse ρ hy hv (by rw [hρB]; rfl) hsv

end OddOrder.RepresentationTheory.Modular
