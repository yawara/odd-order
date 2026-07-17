/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Wielandt's fixed-point formula — the module-level counting (Peterfalvi (9.1))

This file builds the elementary-abelian (= vector-space) core of **Peterfalvi (9.1)**
(Wielandt's fixed-point formula).  The eventual target, assembled in
`OddOrder.GroupTheory.CoprimeAction`, is

`|C_H(UE)|^{|E|} · |H| = |C_H(E)|^{|E|} · |C_H(U)|`

for a Frobenius group `L = U ⋊ E` acting coprimely on a finite solvable group `H`.

The proof reduces, through a chief series of `H`, to a dimension identity on each
elementary-abelian chief factor `V` (an `𝔽_p[L]`-module with `p ∤ |L|`):

`|E| · dim V^L + dim V = |E| · dim V^E + dim V^U`.            (⋆)

See `notes/peterfalvi/s11_wielandt_91_design.md` for the full route.  This file collects
the linear-algebra facts; `S03b_Lemma33` already supplies the *qualitative* Wielandt
lemma (kernel acts trivially), but the present *counting* needs Maschke + Brauer's
permutation lemma instead of the averaging-operator trace.

## Main results (this file, growing bottom-up)

* `finrank_invariants_add_finrank_ker_averageMap`: the coprime decomposition
  `V = V^G ⊕ [V,G]` at the level of dimensions, `dim V^G + dim [V,G] = dim V`.
-/

namespace OddOrder.GroupTheory.WielandtCounting

open Module Representation

variable {k : Type*} [Field k] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- **Coprime decomposition, dimension form.**  When `|G|` is invertible in `k`, the averaging
map `averageMap ρ` is a projection onto the invariants `V^G`, so `V = V^G ⊕ [V,G]` with
`[V,G] = ker (averageMap ρ)`.  Taking dimensions:
`dim V^G + dim [V,G] = dim V`. -/
theorem finrank_invariants_add_finrank_ker_averageMap
    (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)]
    [FiniteDimensional k V] :
    finrank k ρ.invariants + finrank k (LinearMap.ker ρ.averageMap) = finrank k V := by
  have hrange : LinearMap.range ρ.averageMap = ρ.invariants := (isProj_averageMap ρ).range
  rw [← hrange, LinearMap.finrank_range_add_finrank_ker]

/-- Explicit form of the averaging projection: `averageMap ρ v = ⅟|G| • ∑_g ρ g v`. -/
theorem averageMap_apply (ρ : Representation k G V) [Fintype G]
    [Invertible (Fintype.card G : k)] (v : V) :
    ρ.averageMap v = ⅟(Fintype.card G : k) • ∑ g : G, ρ g v := by
  simp only [averageMap, GroupAlgebra.average, map_smul, map_sum, MonoidAlgebra.of_apply,
    asAlgebraHom_single_one, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]

/-- The two summands of the coprime decomposition meet trivially: a `G`-invariant vector lying
in the augmentation submodule `[V,G] = ker (averageMap ρ)` is zero.  (This is `[V,G]^G = 0`, used
to collapse the el-ab identity to the kernel-FPF case.) -/
theorem eq_zero_of_mem_ker_averageMap_of_mem_invariants
    (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)]
    {v : V} (hker : v ∈ LinearMap.ker ρ.averageMap) (hinv : v ∈ ρ.invariants) : v = 0 := by
  rw [LinearMap.mem_ker] at hker
  exact (averageMap_id ρ v hinv).symm.trans hker

/-- The coprime decomposition `V = V^G ⊕ [V,G]`: the invariants and the augmentation submodule
`[V,G] = ker (averageMap ρ)` are complementary. -/
theorem isCompl_invariants_ker_averageMap
    (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)] :
    IsCompl ρ.invariants (LinearMap.ker ρ.averageMap) :=
  (isProj_averageMap ρ).isCompl

/-- If subgroups `H₁, H₂` generate `G` (`H₁ ⊔ H₂ = ⊤`), then the invariants of `ρ` are the
intersection of the invariants of the restrictions `ρ|_{H₁}` and `ρ|_{H₂}`: being fixed by a
generating set forces being fixed by the whole group.  Specialised to `⟨U,E⟩ = L`, this is
`V^{UE} = V^U ⊓ V^E`. -/
theorem invariants_eq_inf_of_sup_eq_top (ρ : Representation k G V) {H₁ H₂ : Subgroup G}
    (hsup : H₁ ⊔ H₂ = ⊤) :
    ρ.invariants = invariants (ρ.comp H₁.subtype) ⊓ invariants (ρ.comp H₂.subtype) := by
  apply le_antisymm
  · exact le_inf (fun v hv s => hv _) (fun v hv s => hv _)
  · intro v hv
    rw [Submodule.mem_inf, mem_invariants, mem_invariants] at hv
    obtain ⟨hv1, hv2⟩ := hv
    -- the stabiliser `{g | ρ g v = v}` is a subgroup containing `H₁` and `H₂`, hence `⊤`.
    let S : Subgroup G :=
      { carrier := {g | ρ g v = v}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at *
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at *
          have h := congrArg (ρ a⁻¹) ha
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] at h
          exact h.symm }
    have hStop : S = ⊤ :=
      top_le_iff.mp (hsup ▸ sup_le (fun g hg => hv1 ⟨g, hg⟩) (fun g hg => hv2 ⟨g, hg⟩))
    exact fun g => (hStop ▸ Subgroup.mem_top g : g ∈ S)

/-- **Fixed points split along an invariant decomposition.**  If `V = A ⊕ B` with both `A`
and `B` stable under every `ρ g`, then the `G`-invariants decompose accordingly:
`dim V^G = dim (A ⊓ V^G) + dim (B ⊓ V^G)`.  (Used with `A = V^U`, `B = [V,U]`, `G = E` to
get `dim V^E = dim V^{UE} + dim ([V,U])^E` in the el-ab identity (⋆).) -/
theorem finrank_invariants_eq_of_isCompl_invariant
    (ρ : Representation k G V) [FiniteDimensional k V]
    {A B : Submodule k V} (hAB : IsCompl A B)
    (hA : ∀ g : G, ∀ a ∈ A, ρ g a ∈ A) (hB : ∀ g : G, ∀ b ∈ B, ρ g b ∈ B) :
    finrank k ρ.invariants =
      finrank k ↥(A ⊓ ρ.invariants) + finrank k ↥(B ⊓ ρ.invariants) := by
  have hdisj : (A ⊓ ρ.invariants) ⊓ (B ⊓ ρ.invariants) = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf inf_le_left inf_le_left) hAB.disjoint.le_bot)
  have hsup : (A ⊓ ρ.invariants) ⊔ (B ⊓ ρ.invariants) = ρ.invariants := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (codisjoint_iff.mp hAB.codisjoint ▸
      Submodule.mem_top (x := v))
    -- `a` and `b` are each `G`-fixed, by uniqueness of the `A ⊕ B` decomposition.
    have hainv : a ∈ ρ.invariants := by
      rw [mem_invariants]
      intro g
      have key : ρ g a + ρ g b = a + b := by rw [← map_add]; exact hv g
      have hba : ρ g a - a = b - ρ g b :=
        sub_eq_sub_iff_add_eq_add.mpr (key.trans (add_comm a b))
      have hmemB : ρ g a - a ∈ B := by rw [hba]; exact B.sub_mem hb (hB g b hb)
      have hzero : ρ g a - a = 0 := by
        rw [← Submodule.mem_bot k, ← hAB.inf_eq_bot]
        exact ⟨A.sub_mem (hA g a ha) ha, hmemB⟩
      exact sub_eq_zero.mp hzero
    have hbinv : b ∈ ρ.invariants := by
      have h := ρ.invariants.sub_mem hv hainv
      rwa [add_sub_cancel_left] at h
    exact Submodule.mem_sup.mpr ⟨a, ⟨ha, hainv⟩, b, ⟨hb, hbinv⟩, rfl⟩
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq
    (A ⊓ ρ.invariants) (B ⊓ ρ.invariants)
  rw [hsup, hdisj, finrank_bot, add_zero] at hrank
  exact hrank

/-- For a normal subgroup `U ◁ G`, the averaging projection over `U` commutes with `ρ g` for any
`g : G`: conjugation by `g` permutes `U`, fixing `∑_{u∈U} ρ u`. -/
theorem ρ_comp_averageMap_comm (ρ : Representation k G V) (U : Subgroup G) [U.Normal]
    [Fintype U] [Invertible (Fintype.card U : k)] (g : G) (v : V) :
    ρ g (averageMap (ρ.comp U.subtype) v) = averageMap (ρ.comp U.subtype) (ρ g v) := by
  rw [averageMap_apply, averageMap_apply, map_smul]
  congr 1
  rw [map_sum]
  refine Fintype.sum_equiv (MulAut.conjNormal g : MulAut U).toEquiv _ _ (fun u => ?_)
  change ρ g (ρ (u : G) v) = ρ (↑(MulAut.conjNormal g u) : G) (ρ g v)
  rw [MulAut.conjNormal_apply]
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- For `U ◁ G`, the augmentation submodule `[V,U] = ker (averageMap ρ|_U)` is `ρ g`-invariant
for every `g : G`. -/
theorem ker_averageMap_comp_invariant (ρ : Representation k G V) (U : Subgroup G) [U.Normal]
    [Fintype U] [Invertible (Fintype.card U : k)] (g : G) :
    ∀ x ∈ LinearMap.ker (averageMap (ρ.comp U.subtype)),
      ρ g x ∈ LinearMap.ker (averageMap (ρ.comp U.subtype)) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← ρ_comp_averageMap_comm ρ U g x, hx, map_zero]

/-- **The elementary-abelian identity (⋆)** for Peterfalvi (9.1), in dimension form, modulo the
kernel-FPF fact (†) supplied as `htag`.  For `ρ` a representation of `G = U ⋊ E` (with `U ◁ G`,
`⟨U,E⟩ = G`) over a field with `|U|` invertible:
`|E|·dim V^{UE} + dim V = |E|·dim V^E + dim V^U`,
provided `dim [V,U] = |E|·dim ([V,U] ⊓ V^E)`  (this is (†), discharged later via Maschke +
the modular Brauer permutation lemma).  Here `V^{UE} = ρ.invariants` since `⟨U,E⟩ = G`. -/
theorem finrank_elab_identity (ρ : Representation k G V) (U E : Subgroup G) [U.Normal]
    [Fintype U] [Fintype E] [Invertible (Fintype.card U : k)] [FiniteDimensional k V]
    (hUE : U ⊔ E = ⊤)
    (htag : finrank k ↥(LinearMap.ker (averageMap (ρ.comp U.subtype))) =
      Fintype.card E * finrank k ↥(LinearMap.ker (averageMap (ρ.comp U.subtype)) ⊓
        invariants (ρ.comp E.subtype))) :
    Fintype.card E * finrank k ↥ρ.invariants + finrank k V =
      Fintype.card E * finrank k ↥(invariants (ρ.comp E.subtype)) +
        finrank k ↥(invariants (ρ.comp U.subtype)) := by
  have hdaf := finrank_invariants_add_finrank_ker_averageMap (ρ.comp U.subtype)
  have hb : finrank k ↥(invariants (ρ.comp E.subtype)) =
      finrank k ↥(invariants (ρ.comp U.subtype) ⊓ invariants (ρ.comp E.subtype)) +
      finrank k ↥(LinearMap.ker (averageMap (ρ.comp U.subtype)) ⊓
        invariants (ρ.comp E.subtype)) := by
    refine finrank_invariants_eq_of_isCompl_invariant (ρ.comp E.subtype)
      (isCompl_invariants_ker_averageMap (ρ.comp U.subtype)) ?_ ?_
    · intro e x hx
      have := le_comap_invariants ρ U (e : G) hx
      rwa [Submodule.mem_comap] at this
    · exact fun e x hx => ker_averageMap_comp_invariant ρ U (e : G) x hx
  rw [invariants_eq_inf_of_sup_eq_top ρ hUE, hb, ← hdaf, htag]
  ring

/-- `ρ a` preserves the dimension of a submodule: `dim (P.map (ρ a)) = dim P`, since `ρ a` is a
linear automorphism.  (When `E` permutes the isotypic components of `W`, each `ρ a` maps one
component isomorphically onto another, so all components in an orbit have equal dimension.) -/
theorem finrank_map_rho_eq (ρ : Representation k G V) (a : G) (P : Submodule k V) :
    finrank k ↥(P.map (ρ a)) = finrank k ↥P := by
  have hinv : Function.LeftInverse (ρ a⁻¹) (ρ a) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  exact (Submodule.equivMapOfInjective (ρ a) hinv.injective P).finrank_eq.symm

/-- **I-3, dimension half.**  If `V = ⊕_{g:G} A g` (internal direct sum) and `ρ` permutes the
summands regularly (`(A e).map (ρ a) = A (a*e)`), then `dim V = |G| · dim (A 1)`: all summands lie
in one regular `G`-orbit, so each `A g = (A 1).map (ρ g)` has dimension `dim (A 1)`. -/
theorem finrank_eq_card_mul_of_regular_orbit (ρ : Representation k G V)
    [Fintype G] [DecidableEq G] [FiniteDimensional k V] {A : G → Submodule k V}
    (hint : DirectSum.IsInternal A) (hperm : ∀ a e : G, (A e).map (ρ a) = A (a * e)) :
    finrank k V = Fintype.card G * finrank k ↥(A 1) := by
  have hW : finrank k V = ∑ g : G, finrank k ↥(A g) := by
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hint).finrank_eq, finrank_directSum]
  have heq : ∀ g : G, finrank k ↥(A g) = finrank k ↥(A 1) := fun g => by
    have hAg : A g = (A 1).map (ρ g) := by rw [hperm g 1, mul_one]
    rw [hAg, finrank_map_rho_eq]
  rw [hW, Finset.sum_congr rfl (fun g _ => heq g), Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **I-3, easy half.**  For `V = ⊕_{g:G} A g` (internal) with `ρ` permuting the summands regularly
and `|G|` invertible, averaging `A 1 → V^G`, `w ↦ averageMap ρ w`, is injective, so
`dim (A 1) ≤ dim V^G`.  Key fact: the `A 1`-component of `averageMap ρ w` is `⅟|G| • w`. -/
theorem finrank_A1_le_finrank_invariants (ρ : Representation k G V)
    [Fintype G] [DecidableEq G] [Invertible (Fintype.card G : k)] [FiniteDimensional k V]
    {A : G → Submodule k V} (hint : DirectSum.IsInternal A)
    (hperm : ∀ a e : G, (A e).map (ρ a) = A (a * e)) :
    finrank k ↥(A 1) ≤ finrank k ↥(invariants ρ) := by
  classical
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hint with he
  have hmem : ∀ (g h : G) (x : V), x ∈ A h → ρ g x ∈ A (g * h) := fun g h x hx =>
    hperm g h ▸ Submodule.mem_map_of_mem hx
  have hcs1 : ∀ (x : V) (hx : x ∈ A 1), e.symm x 1 = ⟨x, hx⟩ := fun x hx => by
    rw [he]; exact hint.ofBijective_coeLinearMap_of_mem hx
  have hcn1 : ∀ (g : G) (x : V), x ∈ A g → g ≠ 1 → e.symm x 1 = 0 := fun g x hx hg => by
    rw [he]; exact hint.ofBijective_coeLinearMap_of_mem_ne hg hx
  have hcomp : ∀ w : ↥(A 1),
      e.symm (averageMap ρ (w : V)) 1 = ⅟(Fintype.card G : k) • w := by
    intro w
    simp only [averageMap_apply, map_smul, map_sum]
    change ⅟(Fintype.card G : k) • ((∑ x : G, e.symm (ρ x (w : V))) 1) = ⅟(Fintype.card G : k) • w
    rw [DirectSum.sum_apply]
    congr 1
    rw [Finset.sum_eq_single (1 : G)]
    · change e.symm (ρ (1 : G) (w : V)) 1 = w
      have h1 : ρ (1 : G) (w : V) ∈ A 1 := by simp
      rw [hcs1 _ h1]; ext; simp
    · intro g _ hg1
      have hg : ρ g (w : V) ∈ A g := by simpa using hmem g 1 (w : V) w.2
      exact hcn1 g _ hg hg1
    · intro h; exact absurd (Finset.mem_univ (1 : G)) h
  let f : ↥(A 1) →ₗ[k] ↥(invariants ρ) :=
    (LinearMap.codRestrict (invariants ρ) (averageMap ρ) (averageMap_invariant ρ)).comp
      (A 1).subtype
  refine LinearMap.finrank_le_finrank_of_injective (f := f) (fun x y hxy => ?_)
  have hav : averageMap ρ (x : V) = averageMap ρ (y : V) := Subtype.ext_iff.mp hxy
  have key : ⅟(Fintype.card G : k) • x = ⅟(Fintype.card G : k) • y := by
    rw [← hcomp x, ← hcomp y, hav]
  have h2 := congrArg (fun z : ↥(A 1) => (Fintype.card G : k) • z) key
  simpa [smul_smul, mul_invOf_self] using h2

set_option linter.unusedFintypeInType false in
/-- **I-3, reverse half.**  For `V = ⊕_{g:G} A g` (internal) with `ρ` permuting regularly, the
`A 1`-component map `V^G → A 1` is injective: an invariant `v` satisfies `v_g = ρ g · v_1`, so it
is determined by `v_1`.  Hence `dim V^G ≤ dim (A 1)`. -/
theorem finrank_invariants_le_finrank_A1 (ρ : Representation k G V)
    [Fintype G] [DecidableEq G] [FiniteDimensional k V]
    {A : G → Submodule k V} (hint : DirectSum.IsInternal A)
    (hperm : ∀ a e : G, (A e).map (ρ a) = A (a * e)) :
    finrank k ↥(invariants ρ) ≤ finrank k ↥(A 1) := by
  classical
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hint with he
  have hmem : ∀ (g h : G) (x : V), x ∈ A h → ρ g x ∈ A (g * h) := fun g h x hx =>
    hperm g h ▸ Submodule.mem_map_of_mem hx
  have hcs : ∀ (j : G) (x : V) (hx : x ∈ A j), e.symm x j = ⟨x, hx⟩ := fun j x hx => by
    rw [he]; exact hint.ofBijective_coeLinearMap_of_mem hx
  have hcn : ∀ (i j : G) (x : V), x ∈ A i → i ≠ j → e.symm x j = 0 := fun i j x hx hij => by
    rw [he]; exact hint.ofBijective_coeLinearMap_of_mem_ne hij hx
  have hdecomp : ∀ v : V, ∑ g : G, ((e.symm v g : ↥(A g)) : V) = v := fun v => by
    have key : ∑ g : G, ((e.symm v g : ↥(A g)) : V) = DirectSum.coeLinearMap A (e.symm v) := by
      conv_rhs => rw [← DirectSum.sum_univ_of (e.symm v), map_sum]
      exact Finset.sum_congr rfl (fun g _ => (DirectSum.coeLinearMap_of A g _).symm)
    rw [key]; exact e.apply_symm_apply v
  -- invariant components: `v_g = ρ g · v_1`
  have hrel : ∀ v ∈ invariants ρ, ∀ g : G, (e.symm v g : V) = ρ g ((e.symm v 1 : ↥(A 1)) : V) := by
    intro v hv g
    have hgv : ρ g v = v := hv g
    have hexp : ρ g v = ∑ h : G, ρ g ((e.symm v h : ↥(A h)) : V) := by
      conv_lhs => rw [← hdecomp v]
      rw [map_sum]
    have : (e.symm (ρ g v) g : V) = ρ g ((e.symm v 1 : ↥(A 1)) : V) := by
      rw [hexp, map_sum, DirectSum.sum_apply]
      rw [Finset.sum_eq_single (1 : G)]
      · have hm : ρ g ((e.symm v 1 : ↥(A 1)) : V) ∈ A g := by simpa using hmem g 1 _ (e.symm v 1).2
        rw [hcs g _ hm]
      · intro h _ hh1
        have hm : ρ g ((e.symm v h : ↥(A h)) : V) ∈ A (g * h) := hmem g h _ (e.symm v h).2
        exact hcn (g * h) g _ hm (fun hc => hh1 (mul_left_cancel (hc.trans (mul_one g).symm)))
      · intro h; exact absurd (Finset.mem_univ (1 : G)) h
    rwa [hgv] at this
  -- the `A 1`-component map, injective on invariants
  let π : ↥(invariants ρ) →ₗ[k] ↥(A 1) :=
    { toFun := fun v => e.symm (v : V) 1
      map_add' := fun x y => by simp [map_add, DirectSum.add_apply]
      map_smul' := fun c x => by simp [map_smul, DirectSum.smul_apply] }
  refine LinearMap.finrank_le_finrank_of_injective (f := π) (fun x y hxy => ?_)
  have h0 : (e.symm ((x : V) - y) 1 : ↥(A 1)) = 0 := by
    rw [map_sub, DirectSum.sub_apply]
    have : e.symm (x : V) 1 = e.symm (y : V) 1 := hxy
    rw [this, sub_self]
  have hsub : (x : V) - (y : V) = 0 := by
    rw [← hdecomp ((x : V) - y)]
    refine Finset.sum_eq_zero (fun g _ => ?_)
    have hxyinv : (x : V) - y ∈ invariants ρ := (invariants ρ).sub_mem x.2 y.2
    rw [hrel _ hxyinv g]
    rw [show (e.symm ((x : V) - y) 1 : ↥(A 1)) = (0 : ↥(A 1)) from h0]
    simp
  exact Subtype.ext (sub_eq_zero.mp hsub)

set_option linter.unusedFintypeInType false in
/-- **I-3, regular-orbit fixed-space count** (capstone).  If `V = ⊕_{g:G} A g` (internal direct
sum) and `ρ` permutes the summands in one regular `G`-orbit (`(A e).map (ρ a) = A (a*e)`), with
`|G|` invertible in `k`, then `dim V = |G| · dim V^G`.  Proof: `dim V = |G|·dim (A 1)` (dimension
half) and `dim (A 1) = dim V^G` (easy + reverse halves, by antisymmetry).

This is the abstract Brauer-free engine behind the kernel-FPF count (†): when the Frobenius
complement `E` permutes the nontrivial `U`-isotypic components of `W` *freely*, each `E`-orbit of
components is a regular `E`-set, so applying this per orbit and summing yields
`dim W = |E|·dim W^E`. -/
theorem finrank_eq_card_mul_finrank_invariants (ρ : Representation k G V)
    [Fintype G] [DecidableEq G] [Invertible (Fintype.card G : k)] [FiniteDimensional k V]
    {A : G → Submodule k V} (hint : DirectSum.IsInternal A)
    (hperm : ∀ a e : G, (A e).map (ρ a) = A (a * e)) :
    finrank k V = Fintype.card G * finrank k ↥(invariants ρ) := by
  rw [finrank_eq_card_mul_of_regular_orbit ρ hint hperm]
  congr 1
  exact le_antisymm (finrank_A1_le_finrank_invariants ρ hint hperm)
    (finrank_invariants_le_finrank_A1 ρ hint hperm)

end OddOrder.GroupTheory.WielandtCounting
