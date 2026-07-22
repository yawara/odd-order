/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyXsetInduction

/-!
# Peterfalvi Appendix IV: the Feit–Sibley endgame (steps (4)–(8))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, pp. 148–150 (campaign issue 1054, endgame).  With `Q₁` a
non-abelian `p`-group, the two coherent families `𝒳 = 𝒮 − 𝒮(Z)` (reduction (3),
`xset_coherent_of_le_center_Q1`) and `𝒴 = 𝒮(Q')` (the Remark,
`ssetOf_Qder_coherent`) are combined into a single coherence of `𝒳 ∪ 𝒴`, which
then extends to `𝒮(S')` and, by reduction (2), to all of `𝒮`.

This file collects the self-contained pieces of the endgame; the coherence
assembly ((4) notation → (5) orthogonality → (6) `a ∣ λ ⟹ 𝒮` coherent → (7)
class-algebra congruence → (8) conclusion) is built on top.

* `x_eq_zero_or_x_one_of_norm_identity` — the (6) integer inequality core
  (p. 148): from the norm identity `1 + a² = (v,v) + a²(x−1)² + (m−1)x²a²` with
  `(v,v) ≥ 0`, `a ≥ 2` and `m ≥ 2`, the only solutions are `x = 0` or
  `x = 1 ∧ m = 2` (the latter reduces to the former by a sign swap of the `e'`).
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped commutatorElement

/-! ## The (6) integer inequality core (p. 148) -/

/-- **Peterfalvi (6) integer core** (p. 148): writing `χ₁(1) = a·d` and expanding
`(Ind(χ₁ − aη₁), Ind(χ₁ − aη₁)) = 1 + a²` through the orthogonal decomposition
`Ind(χ₁ − aη₁) = v − a·e'₁ + λ·∑ e'ᵢ` (with `λ = a·x`) gives the integer identity
`1 + a² = (v,v) + a²(x−1)² + (m−1)·x²·a²`.  Since `(v,v) ≥ 0`, `a ≥ 2` (as
`𝒳 ∩ 𝒴 = ∅` forces `a > 1`) and `m ≥ 2`, the bracket `(x−1)² + (m−1)x²` is at
most `1 + 1/a² < 2`, hence at most `1`: the only integer solutions are `x = 0`
or `x = 1 ∧ m = 2`. -/
theorem x_eq_zero_or_x_one_of_norm_identity {a m x nvv : ℤ}
    (ha : 2 ≤ a) (hm : 2 ≤ m) (hnvv : 0 ≤ nvv)
    (heq : 1 + a ^ 2 = nvv + a ^ 2 * (x - 1) ^ 2 + (m - 1) * x ^ 2 * a ^ 2) :
    x = 0 ∨ (x = 1 ∧ m = 2) := by
  -- `a² · ((x−1)² + (m−1)x²) ≤ 1 + a²`
  have hb : a ^ 2 * ((x - 1) ^ 2 + (m - 1) * x ^ 2) ≤ 1 + a ^ 2 := by nlinarith [heq, hnvv]
  -- integrality: the bracket is `≤ 1`
  have hk : (x - 1) ^ 2 + (m - 1) * x ^ 2 ≤ 1 := by
    by_contra h
    push Not at h
    have h2 : 2 ≤ (x - 1) ^ 2 + (m - 1) * x ^ 2 := h
    nlinarith [hb, ha, h2, mul_nonneg (sq_nonneg a)
      (by linarith : (0 : ℤ) ≤ (x - 1) ^ 2 + (m - 1) * x ^ 2 - 2)]
  -- `(m−1)x² ≥ 0`, so `(x−1)² ≤ 1`, whence `0 ≤ x ≤ 2`
  have hmx : (0 : ℤ) ≤ (m - 1) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  have hx1 : (x - 1) ^ 2 ≤ 1 := by linarith [hk, hmx]
  have hxlo : 0 ≤ x := by nlinarith [hx1, sq_nonneg (x - 1)]
  have hxhi : x ≤ 2 := by nlinarith [hx1, sq_nonneg (x - 1)]
  interval_cases x
  · exact Or.inl rfl
  · -- `x = 1`: the bracket is `m − 1 ≤ 1`, so `m = 2`
    refine Or.inr ⟨rfl, ?_⟩
    have : m - 1 ≤ 1 := by nlinarith [hk]
    omega
  · -- `x = 2`: the bracket is `1 + 4(m−1) ≥ 5 > 1`, impossible
    exfalso
    nlinarith [hk, hm]

/-- **Sign–degree bookkeeping core for Peterfalvi (5)** (p. 148): if the signed
irreducible constituents satisfy the `λ`-equality `e·f₁ = −(A·(e₁·f₂))` (the two
evaluations of `λ = (eᵢ − aᵢe₁, e'ⱼ)`), the `X`-side degree identity
`e·D₂ = A·(e₁·D₁)` (from `(eᵢ − aᵢe₁)(1) = 0`) and the `Y`-side degree identity
`f₂·D₁ = f₁·D₂` (from `(e'₂ − e'₁)(1) = 0`), with `e₁, f₁, f₂` signs and `A ≠ 0`,
then `D₂ = 0` — contradicting the positivity of the degree `D₂ = ξ(1)` at the
call site.  (This is sharper than the book's route via `aᵢ = 1` and
`e'₁(1) = 0`: the same three relations force the `X`-witness degree to vanish
directly.) -/
theorem eq_zero_of_signed_degree_relations {e e₁ f₁ f₂ A D₁ D₂ : ℂ}
    (he₁ : e₁ ^ 2 = 1) (hf₁ : f₁ ^ 2 = 1) (hf₂ : f₂ ^ 2 = 1) (hA : A ≠ 0)
    (H1 : e * f₁ = -(A * (e₁ * f₂)))
    (H2 : e * D₂ = A * (e₁ * D₁))
    (H3 : f₂ * D₁ = f₁ * D₂) : D₂ = 0 := by
  -- `A·(f₁D₁ + f₂D₂) = 0`, by eliminating `e` between `H1` and `H2`
  have hdag : f₁ * D₁ + f₂ * D₂ = 0 := by
    have hkey : A * (f₁ * D₁ + f₂ * D₂) = 0 := by
      linear_combination (-(e₁ * f₁)) * H2 + (e₁ * D₂) * H1
        - A * (f₁ * D₁ + f₂ * D₂) * he₁
    exact (mul_eq_zero.mp hkey).resolve_left hA
  -- combining with `H3` gives `2·D₂ = 0`
  have h2 : (2 : ℂ) * D₂ = 0 := by
    linear_combination f₂ * hdag - f₁ * H3 - D₂ * hf₁ - D₂ * hf₂
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · exact h

section SignedIrr

variable {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]

open scoped Classical in
/-- Inner product of two signed irreducible characters:
`⟨ε•ξ, ε'•ξ'⟩ = ε·ε'·δ_{ξ,ξ'}` (the `star` on the right scalar is invisible for
integer signs).  Upstream candidate for `ZIrrFourier.lean` next to
`irreducibleCharacter_inner_eq_ite`. -/
theorem inner_zsmul_irreducible_eq (ε ε' : ℤ) (ξ ξ' : IrreducibleCharacter Γ) :
    ClassFunction.inner (ε • (ξ : ClassFunction Γ ℂ)) (ε' • (ξ' : ClassFunction Γ ℂ)) =
      (ε : ℂ) * (ε' : ℂ) * (if ξ = ξ' then 1 else 0) := by
  rw [← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction Γ ℂ),
    ← Int.cast_smul_eq_zsmul ℂ ε' (ξ' : ClassFunction Γ ℂ),
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, star_intCast,
    irreducibleCharacter_inner_eq_ite]
  ring

/-- **Residual orthogonality** (Peterfalvi (6), p. 148): subtracting the Fourier
components of `u` along a finite orthonormal family `w` leaves a residual
orthogonal to every member: `(u − ∑ⱼ (u,wⱼ)·wⱼ, wₖ) = 0`.  Upstream candidate
for `ZIrrFourier.lean`. -/
theorem inner_sub_sum_inner_smul_eq_zero {ι : Type*} {s : Finset ι}
    {w : ι → ClassFunction Γ ℂ}
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ClassFunction.inner (w i) (w j) = 0)
    (hnorm : ∀ j ∈ s, ClassFunction.inner (w j) (w j) = 1)
    (u : ClassFunction Γ ℂ) {k : ι} (hk : k ∈ s) :
    ClassFunction.inner (u - ∑ j ∈ s, ClassFunction.inner u (w j) • w j) (w k) = 0 := by
  rw [ClassFunction.inner_sub_left, inner_sum_left s _ _,
    Finset.sum_eq_single k
      (fun j hj hne => by
        rw [ClassFunction.inner_smul_left, horth j hj k hk hne, mul_zero])
      (fun h => absurd hk h),
    ClassFunction.inner_smul_left, hnorm k hk, mul_one, sub_self]

/-- **Bessel decomposition of the norm** (Peterfalvi (6), p. 148): for a finite
orthonormal family `w` and any `u`,
`(u, u) = (v, v) + ∑ⱼ (u,wⱼ)·star (u,wⱼ)` where `v = u − ∑ⱼ (u,wⱼ)·wⱼ` is the
residual.  Upstream candidate for `ZIrrFourier.lean`. -/
theorem inner_self_eq_residual_add_sum_inner_mul_star {ι : Type*} {s : Finset ι}
    {w : ι → ClassFunction Γ ℂ}
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ClassFunction.inner (w i) (w j) = 0)
    (hnorm : ∀ j ∈ s, ClassFunction.inner (w j) (w j) = 1)
    (u : ClassFunction Γ ℂ) :
    ClassFunction.inner u u =
      ClassFunction.inner (u - ∑ j ∈ s, ClassFunction.inner u (w j) • w j)
        (u - ∑ j ∈ s, ClassFunction.inner u (w j) • w j)
      + ∑ j ∈ s, ClassFunction.inner u (w j) * star (ClassFunction.inner u (w j)) := by
  set S : ClassFunction Γ ℂ := ∑ j ∈ s, ClassFunction.inner u (w j) • w j with hS
  set v : ClassFunction Γ ℂ := u - S with hv
  -- the residual is orthogonal to the projection, on both sides
  have hvw : ∀ k ∈ s, ClassFunction.inner v (w k) = 0 := fun k hk =>
    inner_sub_sum_inner_smul_eq_zero horth hnorm u hk
  have hvS : ClassFunction.inner v S = 0 := by
    rw [hS, inner_sum_right]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [ClassFunction.inner_smul_right, hvw j hj, mul_zero]
  have hSv : ClassFunction.inner S v = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hvS, star_zero]
  -- the projection's self-pairing is the diagonal sum
  have hSS : ClassFunction.inner S S = ∑ j ∈ s, ClassFunction.inner u (w j) *
      star (ClassFunction.inner u (w j)) := by
    rw [hS, inner_sum_left]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ClassFunction.inner_smul_left, inner_sum_right,
      Finset.sum_eq_single j
        (fun k hk hne => by
          rw [ClassFunction.inner_smul_right, horth j hj k hk (Ne.symm hne), mul_zero])
        (fun h => absurd hj h),
      ClassFunction.inner_smul_right, hnorm j hj]
    ring
  have hu : u = v + S := by rw [hv]; abel
  calc ClassFunction.inner u u = ClassFunction.inner (v + S) (v + S) := by rw [← hu]
    _ = ClassFunction.inner v v + ClassFunction.inner v S +
        (ClassFunction.inner S v + ClassFunction.inner S S) := by
        rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
          ClassFunction.inner_add_right]
    _ = _ := by rw [hvS, hSv, hSS, add_zero, zero_add]

end SignedIrr

/-! ## The endgame central subgroup `Z = ⁅Q₁, Q₁⁆ ⊓ Z(Q₁)` (Peterfalvi (4), p. 147)

For a non-abelian `p`-group `Q₁` the subgroup `Z = [Q₁,Q₁] ∩ Z(Q₁)` is a
nontrivial `H`-invariant central subgroup of `Q₁`; it supplies the `Z` of
reduction (3) (`xset_coherent_of_le_center_Q1`), so `𝒳 = 𝒮 − 𝒮(Z)` is coherent. -/

namespace Hypothesis

variable {G : Type*} [Group G] (hyp : Hypothesis G)

/-- **The endgame central subgroup** `Z = ⁅Q₁, Q₁⁆ ⊓ C_G(Q₁)` (Peterfalvi (4)).
The intersection with the centralizer realises the `Z(Q₁)`-part: `Z ≤ Q₁` and `Z`
centralises `Q₁`, i.e. `Z ≤ Z(Q₁)`. -/
def endgameZ : Subgroup G := ⁅hyp.Q1, hyp.Q1⁆ ⊓ Subgroup.centralizer (hyp.Q1 : Set G)

/-- `⁅Q₁, Q₁⁆ ≤ Q₁`: a subgroup is closed under commutators. -/
theorem commutator_Q1_le_Q1 : ⁅hyp.Q1, hyp.Q1⁆ ≤ hyp.Q1 :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact hyp.Q1.mul_mem (hyp.Q1.mul_mem (hyp.Q1.mul_mem ha hb) (hyp.Q1.inv_mem ha))
      (hyp.Q1.inv_mem hb)

theorem endgameZ_le_Q1 : hyp.endgameZ ≤ hyp.Q1 := inf_le_left.trans hyp.commutator_Q1_le_Q1

/-- **`Z` centralises `Q₁`** (`Z ≤ Z(Q₁)`): `⁅z, y⁆ = 1` for `z ∈ Z`, `y ∈ Q₁`. -/
theorem endgameZ_centralizes {z : G} (hz : z ∈ hyp.endgameZ) {y : G} (hy : y ∈ hyp.Q1) :
    ⁅z, y⁆ = 1 := by
  have hyz : ⁅y, z⁆ = 1 :=
    (Subgroup.mem_centralizer_iff_commutator_eq_one.mp hz.2) y hy
  have : Commute z y := (commutatorElement_eq_one_iff_commute.mp hyz).symm
  exact commutatorElement_eq_one_iff_commute.mpr this

/-- The `↥Q₁`-level commutator maps onto `⁅Q₁, Q₁⁆`. -/
theorem map_commutator_Q1 :
    (commutator ↥hyp.Q1).map hyp.Q1.subtype = ⁅hyp.Q1, hyp.Q1⁆ := by
  rw [commutator_def, Subgroup.map_commutator]
  simp only [← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- **`Z ≠ ⊥`** for a non-abelian `p`-group `Q₁` (Peterfalvi (4)): the nontrivial
normal subgroup `[Q₁,Q₁]` of the `p`-group `Q₁` meets the centre nontrivially
(`IsPGroup.normal_inf_center_nontrivial`), and the injective `Q₁ ↪ G` carries the
nontriviality up to `Z`. -/
theorem endgameZ_ne_bot [Finite G] {p : ℕ} (hp : p.Prime) (hQ1p : IsPGroup p ↥hyp.Q1)
    (hnonab : ⁅hyp.Q1, hyp.Q1⁆ ≠ ⊥) : hyp.endgameZ ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `commutator ↥Q₁` is nontrivial, else `⁅Q₁,Q₁⁆ = ⊥`
  have hcomm_nt : Nontrivial (commutator ↥hyp.Q1) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hcbot
    exact hnonab (by rw [← hyp.map_commutator_Q1, hcbot, Subgroup.map_bot])
  -- `[Q₁,Q₁] ⊓ Z(Q₁) ≠ ⊥` in `↥Q₁`
  have hK : (commutator ↥hyp.Q1) ⊓ Subgroup.center ↥hyp.Q1 ≠ ⊥ := by
    rw [← Subgroup.nontrivial_iff_ne_bot]
    exact OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hQ1p hcomm_nt
  -- its `G`-image sits inside `Z` and is nontrivial (subtype injective)
  have hmaple : ((commutator ↥hyp.Q1) ⊓ Subgroup.center ↥hyp.Q1).map hyp.Q1.subtype
      ≤ hyp.endgameZ := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hzc, hzcent⟩ := Subgroup.mem_inf.mp hz
    refine ⟨?_, ?_⟩
    · exact hyp.map_commutator_Q1 ▸ Subgroup.mem_map_of_mem hyp.Q1.subtype hzc
    · refine Subgroup.mem_centralizer_iff_commutator_eq_one.mpr fun g hg => ?_
      have hcz : Commute (⟨g, hg⟩ : ↥hyp.Q1) z :=
        (Subgroup.mem_center_iff.mp hzcent) (⟨g, hg⟩ : ↥hyp.Q1)
      have hcomm : Commute g (hyp.Q1.subtype z) := by
        simpa using hcz.map hyp.Q1.subtype
      exact commutatorElement_eq_one_iff_commute.mpr hcomm
  have hmapne : ((commutator ↥hyp.Q1) ⊓ Subgroup.center ↥hyp.Q1).map hyp.Q1.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff]
    exact hK
  exact fun hbot => hmapne (le_bot_iff.mp (by rw [← hbot]; exact hmaple))

/-- **`Z` is `H`-invariant** (element form): `h · x · h⁻¹ ∈ Z` for `h ∈ H`,
`x ∈ Z`.  Both factors are `H`-invariant — `⁅Q₁,Q₁⁆` because `Q₁ ⊴ H`
(`Q1_map_conj_eq` + `map_commutator`), and `C_G(Q₁)` because conjugation permutes
`Q₁`. -/
theorem endgameZ_conj_mem_of_mem_H [Finite G] {h : G} (hh : h ∈ hyp.H)
    {x : G} (hx : x ∈ hyp.endgameZ) : h * x * h⁻¹ ∈ hyp.endgameZ := by
  obtain ⟨hxc, hxcent⟩ := hx
  refine ⟨?_, ?_⟩
  · -- `h·x·h⁻¹ ∈ ⁅Q₁,Q₁⁆`
    have hφ : Subgroup.map (MulAut.conj h).toMonoidHom ⁅hyp.Q1, hyp.Q1⁆ = ⁅hyp.Q1, hyp.Q1⁆ := by
      rw [Subgroup.map_commutator, hyp.Q1_map_conj_eq hh]
    have hmem : (MulAut.conj h) x ∈ ⁅hyp.Q1, hyp.Q1⁆ :=
      hφ ▸ Subgroup.mem_map_of_mem _ hxc
    simpa [MulAut.conj] using hmem
  · -- `h·x·h⁻¹ ∈ C_G(Q₁)`
    refine Subgroup.mem_centralizer_iff_commutator_eq_one.mpr fun y hy => ?_
    have hy' : h⁻¹ * y * h ∈ hyp.Q1 := by
      have := hyp.Q1_normal_in_H (hyp.H.inv_mem hh) hy
      simpa using this
    -- `x` commutes with `h⁻¹yh`; conjugating by `h` gives `hxh⁻¹` commutes with `y`
    have hxc' : ⁅h⁻¹ * y * h, x⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one.mp hxcent) (h⁻¹ * y * h) hy'
    have hc : Commute (h⁻¹ * y * h) x := commutatorElement_eq_one_iff_commute.mp hxc'
    have hcm := hc.map (MulAut.conj h).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcm
    have hyeq : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
    rw [hyeq] at hcm
    exact commutatorElement_eq_one_iff_commute.mpr hcm

/-! ## The two coherent families `𝒳` and `𝒴` (Peterfalvi (4), p. 147) -/

section Coherence

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

/-- **`𝒳 = 𝒮 − 𝒮(Z) = XsetOf ⊥ Z` is coherent** (Peterfalvi (4), reduction (3) at
the endgame `Z = ⁅Q₁,Q₁⁆ ∩ Z(Q₁)`): the four `Z`-hypotheses of
`xset_coherent_of_le_center_Q1` are the `endgameZ_*` facts, and the three `Normal`
instances descend from `Sder`, `Z` and `S` being `H`-invariant. -/
theorem endgame_Xset_coherent (hd : Odd hyp.d) {p : ℕ} (hp : p.Prime)
    (hQ1p : IsPGroup p ↥hyp.Q1) (hnonab : ⁅hyp.Q1, hyp.Q1⁆ ≠ ⊥) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.XsetOf (⊥ : Subgroup G) hyp.endgameZ) hyp.A) := by
  haveI : (hyp.Sder.subgroupOf hyp.H).Normal :=
    hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx => hyp.Sder_conj_mem_of_mem_H hh hx
  haveI : (hyp.endgameZ.subgroupOf hyp.H).Normal :=
    hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx => hyp.endgameZ_conj_mem_of_mem_H hh hx
  haveI : ((hyp.S ⊔ hyp.endgameZ).subgroupOf hyp.H).Normal :=
    hyp.subgroupOf_H_normal_of_conj_mem fun h hh x hx =>
      conj_mem_sup (fun y hy => hyp.S_normal_in_H hh hy)
        (fun y hy => hyp.endgameZ_conj_mem_of_mem_H hh hy) hx
  exact hyp.xset_coherent_of_le_center_Q1 hd hp hQ1p hyp.endgameZ_le_Q1
    (hyp.endgameZ_ne_bot hp hQ1p hnonab)
    (fun z hz y hy => hyp.endgameZ_centralizes hz hy)
    (fun h hh x hx => hyp.endgameZ_conj_mem_of_mem_H hh hx)

omit [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)] in
/-- **The coherence witness at an irreducible member** (Peterfalvi (4)): the
coherent extension of an irreducible `χ ∈ S` is `±` a single irreducible
character of `G` — `extension χ = ε • ξ` with `ε ∈ {±1}`, `ξ ∈ Irr G`.  The
isometry (`extension_inner_eq`) sends `‖χ‖² = 1` to `‖extension χ‖² = 1`, and
`extension χ ∈ ℤ[Irr G]` (`extension_mem_ZIrr`), so
`exists_zsmul_irreducibleCharacter_of_inner_self_one` gives the signed
irreducible.  This yields the witnesses `eᵢ` (from `𝒳`) and `e'ⱼ` (from `𝒴`). -/
theorem coherent_extension_eq_zsmul_irr {S : Set (ClassFunction ↥hyp.H ℂ)} {A : Set ↥hyp.H}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ S) (hχirr : IsIrreducibleCharacter χ) :
    ∃ (ε : ℤ) (ξ : IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧ hcoh.extension χ = ε • (ξ : ClassFunction G ℂ) := by
  have hχspan : χ ∈ OddOrder.Peterfalvi.S07.zSpan S := Submodule.subset_span hχS
  have hmem : hcoh.extension χ ∈ ZIrr G := hcoh.extension_mem_ZIrr χ hχspan
  have hnorm : ClassFunction.inner (hcoh.extension χ) (hcoh.extension χ) = 1 := by
    rw [hcoh.extension_inner_eq χ χ hχspan hχspan]
    exact hχirr.inner_self_eq_one
  exact exists_zsmul_irreducibleCharacter_of_inner_self_one hmem hnorm

/-! ### Peterfalvi (5): the witnesses of `𝒳` and `𝒴` are orthogonal (p. 148)

Both coherent extensions agree with `τ = Ind_H^G` on `A`-supported lattice
elements (`extends_on_supported`), and `τ` is a **global** isometry on the
`A`-supported `𝒮`-sublattice (`tau_inner_eq_of_supported_Sset`), so
cross-family inner products of keystone differences transport back to `H`,
where they vanish (`𝒳 ∩ 𝒴 = ∅` and distinct irreducibles are orthogonal). -/

/-- **Cross-family isometry transport**: for `χ − a•χ₁` supported in `ℤ[X, A]`
and `η − η'` supported in `ℤ[Y, A]` with `X, Y ⊆ 𝒮` disjoint,
`⟨E χ − a·E χ₁, E' η − E' η'⟩ = ⟨χ − a·χ₁, η − η'⟩ = 0`. -/
theorem cross_inner_extension_diff_eq_zero [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ χ₁ : ClassFunction ↥hyp.H ℂ} (hχX : χ ∈ X) (hχ₁X : χ₁ ∈ X) {a : ℕ}
    (hsuppX : χ - a • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {η η' : ClassFunction ↥hyp.H ℂ} (hηY : η ∈ Y) (hη'Y : η' ∈ Y)
    (hsuppY : η - η' ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A) :
    ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
      (hcohY.extension η - hcohY.extension η') = 0 := by
  -- both extensions agree with `τ` on the supported differences
  have hEX : hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁ = hyp.tau (χ - a • χ₁) := by
    rw [← hcohX.extends_on_supported _ hsuppX, map_sub, map_nsmul,
      Nat.cast_smul_eq_nsmul ℂ a (hcohX.extension χ₁)]
  have hEY : hcohY.extension η - hcohY.extension η' = hyp.tau (η - η') := by
    rw [← hcohY.extends_on_supported _ hsuppY, map_sub]
  rw [hEX, hEY, hyp.tau_inner_eq_of_supported_Sset
    (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left hXS hsuppX)
    (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left hYS hsuppY)]
  -- the four member-level cross inner products vanish
  have horth : ∀ φ ∈ X, ∀ ψ ∈ Y, ClassFunction.inner φ ψ = 0 := fun φ hφ ψ hψ =>
    hyp.Sset_pairwiseOrthogonal (hXS hφ) (hYS hψ) (fun h => hdisj φ hφ (h ▸ hψ))
  rw [← Nat.cast_smul_eq_nsmul ℂ a χ₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left]
  rw [horth χ hχX η hηY, horth χ hχX η' hη'Y, horth χ₁ hχ₁X η hηY, horth χ₁ hχ₁X η' hη'Y]
  ring

/-- **Peterfalvi (5), core case** (p. 148): `λ = (eᵢ − aᵢe₁, e'₁) = 0`.  Assuming
`λ ≠ 0`, the two evaluations of `λ` (at `η₁` and `η₂`, equal by the cross
isometry) force the `𝒴`-witnesses `ξ'₁ ≠ ξ'₂` to exhaust the two `𝒳`-witness
irreducibles `{ξχ, ξ₁}`; the sign–degree relations then make the degree `ξχ(1)`
vanish (`eq_zero_of_signed_degree_relations`), a contradiction. -/
theorem cross_inner_extension_diff_right_eq_zero [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ χ₁ : ClassFunction ↥hyp.H ℂ} (hχX : χ ∈ X) (hχ₁X : χ₁ ∈ X) (hχne : χ ≠ χ₁)
    {a : ℕ} (ha : 0 < a)
    (hsuppX : χ - a • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {η₁ η₂ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y) (hη₂Y : η₂ ∈ Y) (hηne : η₂ ≠ η₁)
    (hsuppY : η₂ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A) :
    ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
      (hcohY.extension η₁) = 0 := by
  classical
  by_contra hlam
  -- signed-irreducible witnesses (Peterfalvi (4))
  obtain ⟨εχ, ξχ, hεχ, hEχ⟩ := hyp.coherent_extension_eq_zsmul_irr hcohX hχX (hXS hχX).1
  obtain ⟨ε₁, ξ₁, hε₁, hEχ₁⟩ := hyp.coherent_extension_eq_zsmul_irr hcohX hχ₁X (hXS hχ₁X).1
  obtain ⟨f₁, ξ'₁, hf₁, hE'₁⟩ := hyp.coherent_extension_eq_zsmul_irr hcohY hη₁Y (hYS hη₁Y).1
  obtain ⟨f₂, ξ'₂, hf₂, hE'₂⟩ := hyp.coherent_extension_eq_zsmul_irr hcohY hη₂Y (hYS hη₂Y).1
  -- distinctness of the witnesses within each family (lattice isometry)
  have hξne : ξχ ≠ ξ₁ := by
    intro h
    have h0 : ClassFunction.inner (hcohX.extension χ) (hcohX.extension χ₁) = 0 := by
      rw [hcohX.extension_inner_eq χ χ₁ (Submodule.subset_span hχX)
        (Submodule.subset_span hχ₁X)]
      exact hyp.Sset_pairwiseOrthogonal (hXS hχX) (hXS hχ₁X) hχne
    rw [hEχ, hEχ₁, h, inner_zsmul_irreducible_eq, if_pos rfl, mul_one] at h0
    rcases hεχ with rfl | rfl <;> rcases hε₁ with rfl | rfl <;> norm_num at h0
  have hξ'ne : ξ'₂ ≠ ξ'₁ := by
    intro h
    have h0 : ClassFunction.inner (hcohY.extension η₂) (hcohY.extension η₁) = 0 := by
      rw [hcohY.extension_inner_eq η₂ η₁ (Submodule.subset_span hη₂Y)
        (Submodule.subset_span hη₁Y)]
      exact hyp.Sset_pairwiseOrthogonal (hYS hη₂Y) (hYS hη₁Y) hηne
    rw [hE'₂, hE'₁, h, inner_zsmul_irreducible_eq, if_pos rfl, mul_one] at h0
    rcases hf₂ with rfl | rfl <;> rcases hf₁ with rfl | rfl <;> norm_num at h0
  -- `λ` evaluated at `η₂` equals `λ` evaluated at `η₁`
  have hlam2 : ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
      (hcohY.extension η₂) =
      ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
        (hcohY.extension η₁) := by
    have h := hyp.cross_inner_extension_diff_eq_zero hXS hYS hdisj hcohX hcohY hχX hχ₁X
      hsuppX hη₂Y hη₁Y hsuppY
    rw [ClassFunction.inner_sub_right] at h
    exact sub_eq_zero.mp h
  -- the value of `λ` against a signed irreducible
  have hval : ∀ (f : ℤ) (ξ' : IrreducibleCharacter G),
      ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
        (f • (ξ' : ClassFunction G ℂ)) =
      (εχ : ℂ) * (f : ℂ) * (if ξχ = ξ' then 1 else 0)
        - (a : ℂ) * ((ε₁ : ℂ) * (f : ℂ) * (if ξ₁ = ξ' then 1 else 0)) := by
    intro f ξ'
    rw [hEχ, hEχ₁, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
      inner_zsmul_irreducible_eq, inner_zsmul_irreducible_eq]
  -- `λ ≠ 0` forces `ξ'₁, ξ'₂ ∈ {ξχ, ξ₁}`
  have hmem₁ : ξχ = ξ'₁ ∨ ξ₁ = ξ'₁ := by
    by_contra hc
    push Not at hc
    apply hlam
    rw [hE'₁, hval, if_neg hc.1, if_neg hc.2]
    ring
  have hmem₂ : ξχ = ξ'₂ ∨ ξ₁ = ξ'₂ := by
    by_contra hc
    push Not at hc
    apply hlam
    rw [← hlam2, hE'₂, hval, if_neg hc.1, if_neg hc.2]
    ring
  -- degree data of the `𝒳`-witnesses
  obtain ⟨dχ, hdχpos, hdχeq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ξχ
  have hdχne : (ξχ : ClassFunction G ℂ) (1 : G) ≠ 0 := by
    rw [hdχeq]
    exact_mod_cast hdχpos.ne'
  -- `(E χ − a·E χ₁)(1) = 0` (the difference is `τ` of a degree-zero element)
  have hv1 : (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁) (1 : G) = 0 := by
    have hEX : hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁ = hyp.tau (χ - a • χ₁) := by
      rw [← hcohX.extends_on_supported _ hsuppX, map_sub, map_nsmul,
        Nat.cast_smul_eq_nsmul ℂ a (hcohX.extension χ₁)]
    rw [hEX]
    refine hyp.tau_apply_one ?_
    by_contra h0
    exact hyp.one_notMem_A (hsuppX.2 (ClassFunction.mem_support.mpr h0))
  have hH2 : (εχ : ℂ) * (ξχ : ClassFunction G ℂ) 1 =
      (a : ℂ) * ((ε₁ : ℂ) * (ξ₁ : ClassFunction G ℂ) 1) := by
    rw [hEχ, hEχ₁, ← Int.cast_smul_eq_zsmul ℂ εχ (ξχ : ClassFunction G ℂ),
      ← Int.cast_smul_eq_zsmul ℂ ε₁ (ξ₁ : ClassFunction G ℂ), ClassFunction.sub_apply,
      ClassFunction.smul_apply, ClassFunction.smul_apply, ClassFunction.smul_apply,
      sub_eq_zero] at hv1
    exact hv1
  -- `(E' η₂ − E' η₁)(1) = 0` likewise
  have hw1' : (hcohY.extension η₂ - hcohY.extension η₁) (1 : G) = 0 := by
    have hEY : hcohY.extension η₂ - hcohY.extension η₁ = hyp.tau (η₂ - η₁) := by
      rw [← hcohY.extends_on_supported _ hsuppY, map_sub]
    rw [hEY]
    refine hyp.tau_apply_one ?_
    by_contra h0
    exact hyp.one_notMem_A (hsuppY.2 (ClassFunction.mem_support.mpr h0))
  have hw1 : (f₂ : ℂ) * (ξ'₂ : ClassFunction G ℂ) 1 =
      (f₁ : ℂ) * (ξ'₁ : ClassFunction G ℂ) 1 := by
    rw [hE'₂, hE'₁, ← Int.cast_smul_eq_zsmul ℂ f₂ (ξ'₂ : ClassFunction G ℂ),
      ← Int.cast_smul_eq_zsmul ℂ f₁ (ξ'₁ : ClassFunction G ℂ), ClassFunction.sub_apply,
      ClassFunction.smul_apply, ClassFunction.smul_apply, sub_eq_zero] at hw1'
    exact hw1'
  -- sign squares and `a ≠ 0`
  have hε₁2 : (ε₁ : ℂ) ^ 2 = 1 := by rcases hε₁ with rfl | rfl <;> norm_num
  have hf₁2 : (f₁ : ℂ) ^ 2 = 1 := by rcases hf₁ with rfl | rfl <;> norm_num
  have hf₂2 : (f₂ : ℂ) ^ 2 = 1 := by rcases hf₂ with rfl | rfl <;> norm_num
  have haC : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  -- case analysis: `{ξ'₁, ξ'₂} = {ξχ, ξ₁}` in one of the two orders
  rcases hmem₁ with h1 | h1 <;> rcases hmem₂ with h2 | h2
  · exact hξ'ne (h2.symm.trans h1)
  · -- `ξ'₁ = ξχ`, `ξ'₂ = ξ₁`: `λ@η₁ = εχ·f₁`, `λ@η₂ = −a·ε₁·f₂`
    have hL : (εχ : ℂ) * (f₁ : ℂ) = -((a : ℂ) * ((ε₁ : ℂ) * (f₂ : ℂ))) := by
      have h := hlam2
      rw [hE'₂, hE'₁, hval, hval, if_pos h1, if_neg (fun hh => hξne (hh.trans h2.symm)),
        if_pos h2, if_neg (fun hh => hξne (h1.trans hh.symm))] at h
      linear_combination -h
    have hH3 : (f₂ : ℂ) * (ξ₁ : ClassFunction G ℂ) 1 =
        (f₁ : ℂ) * (ξχ : ClassFunction G ℂ) 1 := by
      rw [← h1, ← h2] at hw1
      exact hw1
    exact hdχne (eq_zero_of_signed_degree_relations hε₁2 hf₁2 hf₂2 haC hL hH2 hH3)
  · -- `ξ'₁ = ξ₁`, `ξ'₂ = ξχ`: `λ@η₁ = −a·ε₁·f₁`, `λ@η₂ = εχ·f₂`
    have hL : (εχ : ℂ) * (f₂ : ℂ) = -((a : ℂ) * ((ε₁ : ℂ) * (f₁ : ℂ))) := by
      have h := hlam2
      rw [hE'₂, hE'₁, hval, hval, if_pos h2, if_neg (fun hh => hξne (h2.trans hh.symm)),
        if_pos h1, if_neg (fun hh => hξne (hh.trans h1.symm))] at h
      linear_combination h
    have hH3 : (f₁ : ℂ) * (ξ₁ : ClassFunction G ℂ) 1 =
        (f₂ : ℂ) * (ξχ : ClassFunction G ℂ) 1 := by
      rw [← h1, ← h2] at hw1
      exact hw1.symm
    exact hdχne (eq_zero_of_signed_degree_relations hε₁2 hf₂2 hf₁2 haC hL hH2 hH3)
  · exact hξ'ne (h2.symm.trans h1)

/-- **Peterfalvi (5), transported to any `η ∈ 𝒴`**: `(eᵢ − aᵢe₁, e'ⱼ) = 0` for
every `j` (the `η₁`-value vanishes by the core case, and the cross isometry
makes the pairing independent of `j`). -/
theorem cross_inner_extension_diff_any_eq_zero [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ χ₁ : ClassFunction ↥hyp.H ℂ} (hχX : χ ∈ X) (hχ₁X : χ₁ ∈ X) (hχne : χ ≠ χ₁)
    {a : ℕ} (ha : 0 < a)
    (hsuppX : χ - a • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {η₁ η₂ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y) (hη₂Y : η₂ ∈ Y) (hηne : η₂ ≠ η₁)
    (hsuppY : η₂ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A)
    {η : ClassFunction ↥hyp.H ℂ} (hηY : η ∈ Y)
    (hsuppη : η - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A) :
    ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
      (hcohY.extension η) = 0 := by
  have h₁ := hyp.cross_inner_extension_diff_right_eq_zero hXS hYS hdisj hcohX hcohY
    hχX hχ₁X hχne ha hsuppX hη₁Y hη₂Y hηne hsuppY
  have h₂ := hyp.cross_inner_extension_diff_eq_zero hXS hYS hdisj hcohX hcohY hχX hχ₁X
    hsuppX hηY hη₁Y hsuppη
  rw [ClassFunction.inner_sub_right, h₁, sub_zero] at h₂
  exact h₂

/-- **Peterfalvi (5)** (p. 148): the coherence witnesses of two disjoint coherent
subfamilies `𝒳, 𝒴 ⊆ 𝒮` are orthogonal — `(eᵢ, e'ⱼ) = 0` for all `i, j`, where
`eᵢ = E(χᵢ)`, `e'ⱼ = E'(ηⱼ)` are the two coherent extensions.  Hypotheses:
`𝒳` has an anchor `χ₁` with all scaled differences `χ − a·χ₁` `A`-supported in
`ℤ[𝒳]` and a second member `χ₂ ≠ χ₁`; `𝒴` has equal degrees (differences
`η − η₁` `A`-supported in `ℤ[𝒴]`) and a second member `η₂ ≠ η₁`. -/
theorem cross_extension_inner_eq_zero [Finite G]
    {X Y : Set (ClassFunction ↥hyp.H ℂ)}
    (hXS : X ⊆ hyp.Sset) (hYS : Y ⊆ hyp.Sset) (hdisj : ∀ φ ∈ X, φ ∉ Y)
    (hcohX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau X hyp.A)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ₁ : ClassFunction ↥hyp.H ℂ} (hχ₁X : χ₁ ∈ X)
    (hXdiff : ∀ φ ∈ X, ∃ a : ℕ, 0 < a ∧
      φ - a • χ₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) X hyp.A)
    {χ₂ : ClassFunction ↥hyp.H ℂ} (hχ₂X : χ₂ ∈ X) (hχ₂ne : χ₂ ≠ χ₁)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y)
    (hYdiff : ∀ ψ ∈ Y, ψ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A)
    {η₂ : ClassFunction ↥hyp.H ℂ} (hη₂Y : η₂ ∈ Y) (hη₂ne : η₂ ≠ η₁)
    {χ η : ClassFunction ↥hyp.H ℂ} (hχX : χ ∈ X) (hηY : η ∈ Y) :
    ClassFunction.inner (hcohX.extension χ) (hcohY.extension η) = 0 := by
  -- Step 1: the anchor pairing `⟨E χ₁, E' η⟩` vanishes
  obtain ⟨a₂, ha₂, hsupp₂⟩ := hXdiff χ₂ hχ₂X
  have hlamEta : ClassFunction.inner (hcohX.extension χ₂ - (a₂ : ℂ) • hcohX.extension χ₁)
      (hcohY.extension η) = 0 :=
    hyp.cross_inner_extension_diff_any_eq_zero hXS hYS hdisj hcohX hcohY hχ₂X hχ₁X hχ₂ne
      ha₂ hsupp₂ hη₁Y hη₂Y hη₂ne (hYdiff η₂ hη₂Y) hηY (hYdiff η hηY)
  have hanchor : ClassFunction.inner (hcohX.extension χ₁) (hcohY.extension η) = 0 := by
    by_contra ht
    obtain ⟨ε₂, ξ₂, hε₂, hE₂⟩ := hyp.coherent_extension_eq_zsmul_irr hcohX hχ₂X (hXS hχ₂X).1
    obtain ⟨ε₁, ξ₁, hε₁, hE₁⟩ := hyp.coherent_extension_eq_zsmul_irr hcohX hχ₁X (hXS hχ₁X).1
    obtain ⟨f, ξ', hf, hE'⟩ := hyp.coherent_extension_eq_zsmul_irr hcohY hηY (hYS hηY).1
    -- the two `𝒳`-witnesses are distinct
    have hξ₂₁ : ξ₂ ≠ ξ₁ := by
      intro h
      have h0 : ClassFunction.inner (hcohX.extension χ₂) (hcohX.extension χ₁) = 0 := by
        rw [hcohX.extension_inner_eq χ₂ χ₁ (Submodule.subset_span hχ₂X)
          (Submodule.subset_span hχ₁X)]
        exact hyp.Sset_pairwiseOrthogonal (hXS hχ₂X) (hXS hχ₁X) hχ₂ne
      rw [hE₂, hE₁, h, inner_zsmul_irreducible_eq, if_pos rfl, mul_one] at h0
      rcases hε₂ with rfl | rfl <;> rcases hε₁ with rfl | rfl <;> norm_num at h0
    -- a nonzero anchor pairing forces `ξ' = ξ₁`
    have hξ' : ξ₁ = ξ' := by
      by_contra hcon
      apply ht
      rw [hE₁, hE', inner_zsmul_irreducible_eq, if_neg hcon, mul_zero]
    -- then `⟨E χ₂, E' η⟩ = 0`, so `hlamEta` reads `a₂ · ⟨E χ₁, E' η⟩ = 0`
    have h₂0 : ClassFunction.inner (hcohX.extension χ₂) (hcohY.extension η) = 0 := by
      rw [hE₂, hE', inner_zsmul_irreducible_eq,
        if_neg (fun hh => hξ₂₁ (hh.trans hξ'.symm)), mul_zero]
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h₂0, zero_sub,
      neg_eq_zero, mul_eq_zero] at hlamEta
    rcases hlamEta with h | h
    · exact (Nat.cast_ne_zero.mpr ha₂.ne') h
    · exact ht h
  -- Step 2: split on `χ = χ₁`
  by_cases hcase : χ = χ₁
  · rw [hcase]
    exact hanchor
  · obtain ⟨a, hapos, hsupp⟩ := hXdiff χ hχX
    have hlam0 : ClassFunction.inner (hcohX.extension χ - (a : ℂ) • hcohX.extension χ₁)
        (hcohY.extension η) = 0 :=
      hyp.cross_inner_extension_diff_any_eq_zero hXS hYS hdisj hcohX hcohY hχX hχ₁X hcase
        hapos hsupp hη₁Y hη₂Y hη₂ne (hYdiff η₂ hη₂Y) hηY (hYdiff η hηY)
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hanchor, mul_zero,
      sub_zero] at hlam0
    exact hlam0

/-! ### Peterfalvi (6): the pairing identities of `Ind(χ₁ − a·η₁)` (p. 148)

With `χ₁ ∈ 𝒳` of degree `a·d` and `η₁ ∈ 𝒴` of degree `d`, the element
`δ = χ₁ − a·η₁` is a degree-zero `A`-supported element of `ℤ[𝒮]`, so `τδ = Ind δ`
is controlled by the Lemma 2(b) isometry: `(τδ, τδ) = 1 + a²` and
`(τδ, e'ⱼ − e'₁) = a` for `j > 1`.  These feed the orthogonal decomposition
`τδ = −a·e'₁ + λ·∑ e'ᵢ + v` of (6). -/

omit [Fintype ↥hyp.H] in
/-- **Peterfalvi (6), norm identity** (p. 148): `(Ind(χ − a·η₁), Ind(χ − a·η₁)) = 1 + a²`
for distinct members `χ, η₁` of `𝒮` with `χ − a·η₁` an `A`-supported lattice
element.  Pure Lemma 2(b): no coherence input. -/
theorem tau_scaled_diff_inner_self [Finite G]
    {χ η₁ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ hyp.Sset) (hη₁S : η₁ ∈ hyp.Sset)
    (hne : χ ≠ η₁) {a : ℕ}
    (hsupp : χ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      hyp.Sset hyp.A) :
    ClassFunction.inner (hyp.tau (χ - a • η₁)) (hyp.tau (χ - a • η₁)) =
      1 + (a : ℂ) ^ 2 := by
  letI : Fintype ↥hyp.H := Fintype.ofFinite _
  rw [hyp.tau_inner_eq_of_supported_Sset hsupp hsupp, ← Nat.cast_smul_eq_nsmul ℂ a η₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, star_natCast]
  rw [(hχS.1).inner_self_eq_one, (hη₁S.1).inner_self_eq_one,
    hyp.Sset_pairwiseOrthogonal hχS hη₁S hne,
    hyp.Sset_pairwiseOrthogonal hη₁S hχS (Ne.symm hne)]
  ring

/-- **Peterfalvi (6), cross pairing** (p. 148): `(Ind(χ − a·η₁), e'ⱼ − e'₁) = a` for
`j > 1` — the isometry sends the pairing back to `H`, where only the
`a·(η₁, η₁)`-term survives.  This determines the `e'`-coefficients of
`Ind(χ₁ − a·η₁)` up to the common shift `λ`. -/
theorem tau_scaled_diff_inner_extension_diff [Finite G]
    {Y : Set (ClassFunction ↥hyp.H ℂ)} (hYS : Y ⊆ hyp.Sset)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ hyp.Sset) (hχY : χ ∉ Y)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y) {a : ℕ}
    (hsupp : χ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      hyp.Sset hyp.A)
    {η : ClassFunction ↥hyp.H ℂ} (hηY : η ∈ Y) (hne : η ≠ η₁)
    (hsuppY : η - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H) Y hyp.A) :
    ClassFunction.inner (hyp.tau (χ - a • η₁))
      (hcohY.extension η - hcohY.extension η₁) = (a : ℂ) := by
  have hEY : hcohY.extension η - hcohY.extension η₁ = hyp.tau (η - η₁) := by
    rw [← hcohY.extends_on_supported _ hsuppY, map_sub]
  rw [hEY, hyp.tau_inner_eq_of_supported_Sset hsupp
    (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left hYS hsuppY),
    ← Nat.cast_smul_eq_nsmul ℂ a η₁]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left]
  rw [hyp.Sset_pairwiseOrthogonal hχS (hYS hηY) (fun h => hχY (h ▸ hηY)),
    hyp.Sset_pairwiseOrthogonal hχS (hYS hη₁Y) (fun h => hχY (h ▸ hη₁Y)),
    hyp.Sset_pairwiseOrthogonal (hYS hη₁Y) (hYS hηY) (Ne.symm hne),
    ((hYS hη₁Y).1).inner_self_eq_one]
  ring

/-- **Peterfalvi (6), the `λ`-form norm identity** (p. 148): for `δ = χ − a·η₁`
(`χ ∈ 𝒮 ∖ 𝒴` of degree `a·d`), the Fourier coefficients of `u = Ind δ` along the
witnesses `e'ⱼ` are `λ` at every `ηⱼ ≠ η₁` and `λ − a` at `η₁`, and the Bessel
decomposition of `(u, u) = 1 + a²` gives the integer identity
`1 + a² = (v,v) + (λ−a)² + (m−1)·λ²` with `(v,v) ≥ 0` and `m = |𝒴|`.
Combining with `a ∣ λ` (from (7)/(8)) this feeds
`x_eq_zero_or_x_one_of_norm_identity`. -/
theorem exists_lambda_norm_identity [Finite G]
    {Y : Set (ClassFunction ↥hyp.H ℂ)} (hYS : Y ⊆ hyp.Sset)
    (hcohY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Y hyp.A)
    {χ : ClassFunction ↥hyp.H ℂ} (hχS : χ ∈ hyp.Sset) (hχY : χ ∉ Y)
    {η₁ : ClassFunction ↥hyp.H ℂ} (hη₁Y : η₁ ∈ Y) {a : ℕ}
    (hsupp : χ - a • η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      hyp.Sset hyp.A)
    (hYdiff : ∀ ψ ∈ Y, ψ - η₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.H)
      Y hyp.A) :
    ∃ lam : ℤ,
      (∀ η ∈ Y, η ≠ η₁ →
        ClassFunction.inner (hyp.tau (χ - a • η₁)) (hcohY.extension η) = (lam : ℂ)) ∧
      ClassFunction.inner (hyp.tau (χ - a • η₁)) (hcohY.extension η₁) = (lam : ℂ) - a ∧
      ∃ nvv : ℤ, 0 ≤ nvv ∧
        1 + (a : ℤ) ^ 2 = nvv + (lam - a) ^ 2 + ((Y.ncard : ℤ) - 1) * lam ^ 2 := by
  classical
  have hYfin : Y.Finite := hyp.Sset_finite.subset hYS
  set s : Finset (ClassFunction ↥hyp.H ℂ) := hYfin.toFinset with hs
  have hmem : ∀ {η : ClassFunction ↥hyp.H ℂ}, η ∈ s ↔ η ∈ Y := fun {η} =>
    Set.Finite.mem_toFinset hYfin
  set u : ClassFunction G ℂ := hyp.tau (χ - a • η₁) with hu
  have huZ : u ∈ ZIrr G := hyp.tau_mem_ZIrr hsupp.1
  -- orthonormality of the `𝒴`-witnesses
  have horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ClassFunction.inner (hcohY.extension i) (hcohY.extension j) = 0 := by
    intro i hi j hj hne
    rw [hcohY.extension_inner_eq i j (Submodule.subset_span (hmem.mp hi))
      (Submodule.subset_span (hmem.mp hj))]
    exact hyp.Sset_pairwiseOrthogonal (hYS (hmem.mp hi)) (hYS (hmem.mp hj)) hne
  have hnorm : ∀ j ∈ s, ClassFunction.inner (hcohY.extension j) (hcohY.extension j) = 1 := by
    intro j hj
    rw [hcohY.extension_inner_eq j j (Submodule.subset_span (hmem.mp hj))
      (Submodule.subset_span (hmem.mp hj))]
    exact ((hYS (hmem.mp hj)).1).inner_self_eq_one
  -- integrality of the Fourier coefficients
  have hint : ∀ η, η ∈ Y → ∃ t : ℤ,
      ClassFunction.inner u (hcohY.extension η) = (t : ℂ) := by
    intro η hη
    obtain ⟨ε, ξ, hε, hE⟩ := hyp.coherent_extension_eq_zsmul_irr hcohY hη (hYS hη).1
    obtain ⟨t0, ht0⟩ := mem_ZIrr_inner_int ξ huZ
    refine ⟨ε * t0, ?_⟩
    rw [hE, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ),
      ClassFunction.inner_smul_right, star_intCast, ht0]
    push_cast
    ring
  choose tz htz using hint
  set c : ClassFunction ↥hyp.H ℂ → ℤ := fun η => if h : η ∈ Y then tz η h else 0 with hcdef
  have hc : ∀ η (hη : η ∈ Y),
      ClassFunction.inner u (hcohY.extension η) = (c η : ℂ) := by
    intro η hη
    rw [hcdef]
    simp only [dif_pos hη]
    exact htz η hη
  -- the common `λ`
  refine ⟨c η₁ + a, ?_, ?_, ?_⟩
  · -- coefficient at `η ≠ η₁`
    intro η hη hne
    have h6a := hyp.tau_scaled_diff_inner_extension_diff hYS hcohY hχS hχY hη₁Y hsupp hη
      hne (hYdiff η hη)
    rw [ClassFunction.inner_sub_right, ← hu] at h6a
    rw [sub_eq_iff_eq_add.mp h6a, hc η₁ hη₁Y]
    push_cast
    ring
  · -- coefficient at `η₁`
    rw [hc η₁ hη₁Y]
    push_cast
    ring
  · -- the Bessel identity
    have hη₁s : η₁ ∈ s := hmem.mpr hη₁Y
    have hBessel := inner_self_eq_residual_add_sum_inner_mul_star horth hnorm u
    -- left side: `(u,u) = 1 + a²`
    have hχη₁ : χ ≠ η₁ := fun h => hχY (h ▸ hη₁Y)
    have huu : ClassFunction.inner u u = 1 + (a : ℂ) ^ 2 := by
      rw [hu]
      exact hyp.tau_scaled_diff_inner_self hχS (hYS hη₁Y) hχη₁ hsupp
    rw [huu] at hBessel
    -- rewrite the residual with integer coefficients
    have hsum_eq : ∑ η ∈ s, ClassFunction.inner u (hcohY.extension η) • hcohY.extension η
        = ∑ η ∈ s, ((c η : ℂ)) • hcohY.extension η :=
      Finset.sum_congr rfl fun η hη => by rw [hc η (hmem.mp hη)]
    rw [hsum_eq] at hBessel
    -- the residual is a virtual character, so its self-pairing is a sum of squares
    have hvZ : u - ∑ η ∈ s, ((c η : ℂ)) • hcohY.extension η ∈ ZIrr G := by
      refine Submodule.sub_mem _ huZ (Submodule.sum_mem _ fun η hη => ?_)
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _
        (hcohY.extension_mem_ZIrr η (Submodule.subset_span (hmem.mp hη)))
    obtain ⟨cf, -, -, hvv⟩ := mem_ZIrr_inner_self_eq_sum_sq hvZ
    refine ⟨∑ α ∈ cf.support, (cf α) ^ 2,
      Finset.sum_nonneg fun α _ => sq_nonneg _, ?_⟩
    -- the coefficient sum: `η₁`-term plus `(m−1)` copies of `λ²`
    have hsum_coeff : ∑ η ∈ s, ClassFunction.inner u (hcohY.extension η) *
        star (ClassFunction.inner u (hcohY.extension η)) =
        ((c η₁ : ℂ)) ^ 2 + ((s.card : ℂ) - 1) * ((c η₁ : ℂ) + a) ^ 2 := by
      rw [← Finset.add_sum_erase s _ hη₁s, hc η₁ hη₁Y, star_intCast]
      congr 1
      · ring
      · have herase : ∀ η ∈ s.erase η₁,
            ClassFunction.inner u (hcohY.extension η) *
              star (ClassFunction.inner u (hcohY.extension η)) =
            ((c η₁ : ℂ) + a) ^ 2 := by
          intro η hη
          obtain ⟨hne, hηs⟩ := Finset.mem_erase.mp hη
          have h6a := hyp.tau_scaled_diff_inner_extension_diff hYS hcohY hχS hχY hη₁Y
            hsupp (hmem.mp hηs) hne (hYdiff η (hmem.mp hηs))
          rw [ClassFunction.inner_sub_right, ← hu] at h6a
          rw [sub_eq_iff_eq_add.mp h6a, hc η₁ hη₁Y]
          rw [show ((a : ℂ)) + (c η₁ : ℂ) = (((c η₁ : ℤ) + (a : ℤ) : ℤ) : ℂ) by push_cast; ring,
            star_intCast]
          push_cast
          ring
        rw [Finset.sum_congr rfl herase, Finset.sum_const, Finset.card_erase_of_mem hη₁s,
          nsmul_eq_mul]
        rw [Nat.cast_sub (Finset.card_pos.mpr ⟨η₁, hη₁s⟩)]
        push_cast
        ring
    rw [hsum_coeff, hvv] at hBessel
    -- cast the `ℂ`-identity down to `ℤ`
    have hcardN : Y.ncard = s.card := by
      rw [hs]
      exact Set.ncard_eq_toFinset_card Y hYfin
    have hZidentity : ((1 + (a : ℤ) ^ 2 : ℤ) : ℂ) =
        ((∑ α ∈ cf.support, (cf α) ^ 2 + ((c η₁ + a) - a) ^ 2 +
          ((Y.ncard : ℤ) - 1) * (c η₁ + a) ^ 2 : ℤ) : ℂ) := by
      rw [hcardN]
      push_cast
      linear_combination hBessel
    exact_mod_cast hZidentity

end Coherence

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
