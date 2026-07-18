/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.BruhatCoordinates

/-!
# Bruhat decomposition for the standard projective unitary group

The coordinate calculation from Peterfalvi, Part II, Chapter IV, Section 3
gives the nontrivial Weyl--root relation in the repository's left-action
coordinates:

`w R(u) w = R(J F J(u)) T(b / star(b)^2) w R(F(u))`.

Here `F` is Peterfalvi's right-action reciprocal and `J F J` is its transport
to left affine coordinates.  This file uses that concrete relation to prove
the two-cell decomposition corresponding to Part II, Chapter I §1,
Proposition 4(a), whose canonical form is `G ∖ H = H t H = H t Q`.  It then
identifies the standard Borel with the stabilizer of infinity and computes the
exact order of the generated permutation group.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

noncomputable section

variable {n : ℕ}

section /- Part II, Chapter IV §3: the nontrivial Bruhat relation -/

namespace Unital

variable {n : ℕ}

/-- The concrete nontrivial Bruhat relation for a root generator.  In the
repository's left-action convention it is

`w R(u) w = R(JFJ(u)) T(b / star(b)²) w R(F(u))`.
-/
theorem weylPerm_mul_rootPerm_mul_weylPerm_eq_bruhat
    (u : RootGroup n) (hu : u ≠ 1) (hn : 0 < n) :
    weylPerm n * rootPermHom n u * weylPerm n =
      rootPermHom n (RootGroup.weylReciprocal u hu) *
        psuTorusPerm n (bruhatTorus u hu hn) * weylPerm n *
          rootPermHom n (RootGroup.reciprocal u hu) := by
  have hrootAffine (a b : RootGroup n) :
      rootPermHom n a (affine b) = affine (a * b) := rfl
  have hrootInfinity (a : RootGroup n) :
      rootPermHom n a (infinity n) = infinity n := rfl
  apply Equiv.Perm.ext
  intro p
  cases p with
  | none =>
      change weylPerm n
          (rootPermHom n u (weylPerm n (infinity n))) =
        rootPermHom n (RootGroup.weylReciprocal u hu)
          (psuTorusPerm n (bruhatTorus u hu hn)
            (weylPerm n
              (rootPermHom n (RootGroup.reciprocal u hu)
                (infinity n))))
      rw [weylPerm_infinity, hrootAffine, hrootInfinity,
        weylPerm_infinity, psuTorusPerm_apply, torusPerm_affine,
        hrootAffine]
      rw [mul_one, weylPerm_affine_of_ne_one u hu,
        RootGroup.scalePoint_one_point, mul_one]
  | some v =>
      change weylPerm n
          (rootPermHom n u (weylPerm n (affine v))) =
        rootPermHom n (RootGroup.weylReciprocal u hu)
          (psuTorusPerm n (bruhatTorus u hu hn)
            (weylPerm n
              (rootPermHom n (RootGroup.reciprocal u hu)
                (affine v))))
      by_cases hv : v = 1
      · subst v
        rw [weylPerm_origin, hrootInfinity, weylPerm_infinity]
        rw [hrootAffine, mul_one]
        rw [weylPerm_affine_of_ne_one _
          (RootGroup.reciprocal_ne_one u hu)]
        rw [psuTorusPerm_apply, torusPerm_affine, hrootAffine]
        exact congrArg affine (origin_bruhat_identity u hu).symm
      · by_cases hpole : RootGroup.reciprocal u hu * v = 1
        · have hleft : u * RootGroup.weylReciprocal v hv = 1 :=
            (mul_weylReciprocal_eq_one_iff_reciprocal_mul_eq_one
              u v hu hv).mpr hpole
          rw [weylPerm_affine_of_ne_one v hv, hrootAffine, hleft,
            weylPerm_origin]
          rw [hrootAffine, hpole, weylPerm_origin,
            psuTorusPerm_apply, torusPerm_infinity, hrootInfinity]
        · have hleft : u * RootGroup.weylReciprocal v hv ≠ 1 :=
            mt (mul_weylReciprocal_eq_one_iff_reciprocal_mul_eq_one
              u v hu hv).mp hpole
          rw [weylPerm_affine_of_ne_one v hv, hrootAffine,
            weylPerm_affine_of_ne_one _ hleft]
          rw [hrootAffine, weylPerm_affine_of_ne_one _ hpole,
            psuTorusPerm_apply, torusPerm_affine, hrootAffine]
          exact congrArg affine
            (generic_bruhat_identity u v hu hv hleft hpole)

end Unital

end


section /- Part II, Chapter I §1, Proposition 4(a): abstract closure -/

/-- The union of the two standard Bruhat cells `B` and `B w B`. -/
def InStandardBruhatCells (g : standardPermGroup n) : Prop :=
  g ∈ standardBorel n ∨
    ∃ b₁ ∈ standardBorel n, ∃ b₂ ∈ standardBorel n,
      g = b₁ * weylElement n * b₂

/-- The concrete relation needed by the abstract two-cell closure argument:
every nontrivial Weyl--root--Weyl product belongs to `B w B`. -/
structure StandardBruhatRelations (n : ℕ) : Prop where
  weyl_root_eq : ∀ u : RootGroup n, u ≠ 1 →
    ∃ b₁ ∈ standardBorel n, ∃ b₂ ∈ standardBorel n,
      weylElement n * rootHom n u * weylElement n =
        b₁ * weylElement n * b₂

variable (n : ℕ)

private theorem one_mem_standardBruhatCells :
    InStandardBruhatCells (n := n) 1 :=
  Or.inl (standardBorel n).one_mem

private theorem borel_mul_mem_standardBruhatCells
    {b g : standardPermGroup n}
    (hb : b ∈ standardBorel n) (hg : InStandardBruhatCells g) :
    InStandardBruhatCells (b * g) := by
  rcases hg with hg | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact Or.inl ((standardBorel n).mul_mem hb hg)
  · right
    exact ⟨b * b₁, (standardBorel n).mul_mem hb hb₁, b₂, hb₂, by
      simp only [mul_assoc]⟩

private theorem mul_borel_mem_standardBruhatCells
    {g b : standardPermGroup n}
    (hg : InStandardBruhatCells g) (hb : b ∈ standardBorel n) :
    InStandardBruhatCells (g * b) := by
  rcases hg with hg | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact Or.inl ((standardBorel n).mul_mem hg hb)
  · right
    exact ⟨b₁, hb₁, b₂ * b, (standardBorel n).mul_mem hb₂ hb, by
      simp only [mul_assoc]⟩

private theorem one_mul_mem_standardBruhatCells
    {g : standardPermGroup n} (hg : InStandardBruhatCells g) :
    InStandardBruhatCells (1 * g) := by
  simpa only [one_mul] using hg

private theorem rootHom_mul_mem_standardBruhatCells
    (u : RootGroup n) {g : standardPermGroup n}
    (hg : InStandardBruhatCells g) :
    InStandardBruhatCells (rootHom n u * g) :=
  borel_mul_mem_standardBruhatCells n (rootHom_mem_standardBorel u) hg

private theorem psuTorusHom_mul_mem_standardBruhatCells
    (c : PSUTorusParameter n) {g : standardPermGroup n}
    (hg : InStandardBruhatCells g) :
    InStandardBruhatCells (psuTorusHom n c * g) :=
  borel_mul_mem_standardBruhatCells n (psuTorusHom_mem_standardBorel c) hg

private theorem weyl_mul_mem_standardBruhatCells
    (hrel : StandardBruhatRelations n)
    {g : standardPermGroup n} (hg : InStandardBruhatCells g) :
    InStandardBruhatCells (weylElement n * g) := by
  have hw : weylElement n * weylElement n = 1 := by
    simpa only [pow_two] using weylElement_sq_eq_one n
  rcases hg with hg | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · right
    exact ⟨1, (standardBorel n).one_mem, g, hg, by simp⟩
  · obtain ⟨p, hp, -⟩ :=
      (mem_standardBorel_iff_existsUnique_root_torus b₁).mp hb₁
    rcases p with ⟨u, c⟩
    have hroot :
        InStandardBruhatCells
          (weylElement n * rootHom n u * weylElement n) := by
      by_cases hu : u = 1
      · left
        subst u
        simpa only [map_one, mul_one, hw] using (standardBorel n).one_mem
      · exact Or.inr (hrel.weyl_root_eq u hu)
    have htorus :
        weylElement n * psuTorusHom n c * weylElement n ∈
          standardBorel n := by
      rw [weylElement_mul_psuTorusHom_mul_weylElement]
      exact psuTorusHom_mem_standardBorel _
    have hcore := mul_borel_mem_standardBruhatCells n hroot htorus
    have hfactor :
        weylElement n * (rootHom n u * psuTorusHom n c) * weylElement n =
          (weylElement n * rootHom n u * weylElement n) *
            (weylElement n * psuTorusHom n c * weylElement n) := by
      calc
        _ = weylElement n * rootHom n u * psuTorusHom n c *
              weylElement n := by
          ac_rfl
        _ = weylElement n * rootHom n u * 1 * psuTorusHom n c *
              weylElement n := by
          simp only [mul_one]
        _ = weylElement n * rootHom n u *
              (weylElement n * weylElement n) * psuTorusHom n c *
                weylElement n := by
          rw [hw]
        _ = _ := by ac_rfl
    have hconj :
        InStandardBruhatCells
          (weylElement n * b₁ * weylElement n) := by
      rw [hp, hfactor]
      exact hcore
    have hfinal := mul_borel_mem_standardBruhatCells n hconj hb₂
    simpa only [mul_assoc] using hfinal

/-- The standard generating set is closed under inversion. -/
private theorem inv_mem_standardGeneratorSet
    {x : Equiv.Perm (Unital n)} (hx : x ∈ standardGeneratorSet n) :
    x⁻¹ ∈ standardGeneratorSet n := by
  rcases hx with ⟨u, rfl⟩ | (⟨c, rfl⟩ | hx)
  · exact Or.inl ⟨u⁻¹, map_inv (Unital.rootPermHom n) u⟩
  · exact Or.inr (Or.inl ⟨c⁻¹, map_inv (Unital.psuTorusPerm n) c⟩)
  · have hxw : x = Unital.weylPerm n := by
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    right
    right
    rw [Set.mem_singleton_iff]
    rfl

private theorem standardGenerator_mul_mem_standardBruhatCells
    (hrel : StandardBruhatRelations n)
    {x : Equiv.Perm (Unital n)} (hx : x ∈ standardGeneratorSet n)
    {g : standardPermGroup n} (hg : InStandardBruhatCells g) :
    InStandardBruhatCells
      ((⟨x, Subgroup.subset_closure hx⟩ : standardPermGroup n) * g) := by
  rcases hx with ⟨u, rfl⟩ | (⟨c, rfl⟩ | hx)
  · change InStandardBruhatCells (rootHom n u * g)
    exact rootHom_mul_mem_standardBruhatCells n u hg
  · change InStandardBruhatCells (psuTorusHom n c * g)
    exact psuTorusHom_mul_mem_standardBruhatCells n c hg
  · have hxw : x = Unital.weylPerm n := by
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    change InStandardBruhatCells (weylElement n * g)
    exact weyl_mul_mem_standardBruhatCells n hrel hg

private theorem mem_standardBruhatCells
    (hrel : StandardBruhatRelations n) (g : standardPermGroup n) :
    InStandardBruhatCells g := by
  let P : (x : Equiv.Perm (Unital n)) →
      x ∈ Subgroup.closure (standardGeneratorSet n) → Prop :=
    fun x hx ↦ ∀ y : standardPermGroup n, InStandardBruhatCells y →
      InStandardBruhatCells
        ((⟨x, hx⟩ : standardPermGroup n) * y)
  have hP : P (g : Equiv.Perm (Unital n)) g.property := by
    apply Subgroup.closure_induction_left (p := P)
    · intro y hy
      change InStandardBruhatCells ((1 : standardPermGroup n) * y)
      exact one_mul_mem_standardBruhatCells n hy
    · intro x hx y hy ih z hz
      have hyz := ih z hz
      have hxyz :=
        standardGenerator_mul_mem_standardBruhatCells n hrel hx hyz
      change InStandardBruhatCells
        (((⟨x, Subgroup.subset_closure hx⟩ : standardPermGroup n) *
          (⟨y, hy⟩ : standardPermGroup n)) * z)
      simpa only [mul_assoc] using hxyz
    · intro x hx y hy ih z hz
      have hyz := ih z hz
      have hxyz := standardGenerator_mul_mem_standardBruhatCells n hrel
        (inv_mem_standardGeneratorSet n hx) hyz
      change InStandardBruhatCells
        (((⟨x⁻¹, Subgroup.subset_closure
              (inv_mem_standardGeneratorSet n hx)⟩ : standardPermGroup n) *
          (⟨y, hy⟩ : standardPermGroup n)) * z)
      simpa only [mul_assoc] using hxyz
  have hg := hP 1 (one_mem_standardBruhatCells n)
  simpa only [mul_one] using hg

end

section /- Part II, Chapter IV §3: concrete Weyl--root relation -/

/-- The source-correct coordinate factorization supplies the nontrivial
relation used in the two-cell closure proof.  The left Borel factor contains
`J F J(u)` and `b / star(b)^2`; the right factor contains Peterfalvi's `F(u)`.
-/
theorem standardBruhatRelations (n : ℕ) (hn : 0 < n) :
    StandardBruhatRelations n where
  weyl_root_eq u hu := by
    refine ⟨rootHom n (RootGroup.weylReciprocal u hu) *
          psuTorusHom n (bruhatTorus u hu hn),
      (standardBorel n).mul_mem (rootHom_mem_standardBorel _)
        (psuTorusHom_mem_standardBorel _),
      rootHom n (RootGroup.reciprocal u hu),
      rootHom_mem_standardBorel _, ?_⟩
    apply Subtype.ext
    exact Unital.weylPerm_mul_rootPerm_mul_weylPerm_eq_bruhat u hu hn

end

section /- Part II, Chapter I §1, Proposition 4(a): two cells -/

/-- **Peterfalvi Part II, Ch. I §1, Prop. 4(a)** (canonical form
`G ∖ H = H t H = H t Q`). Every element of the standard projective unitary
group lies in `B` or in `B w B`. -/
theorem standardBruhatDecomposition
    (n : ℕ) (hn : 0 < n) (g : standardPermGroup n) :
    InStandardBruhatCells g :=
  mem_standardBruhatCells n (standardBruhatRelations n hn) g

/-- **Peterfalvi Part II, Ch. I §1, Prop. 4(a), standard-model stabilizer
analogue.** The standard Borel subgroup is exactly the stabilizer of infinity. -/
theorem standardBorel_eq_infinityStabilizer
    (n : ℕ) (hn : 0 < n) :
    standardBorel n =
      MulAction.stabilizer (standardPermGroup n) (Unital.infinity n) := by
  apply le_antisymm standardBorel_le_infinityStabilizer
  intro g hg
  rcases standardBruhatDecomposition n hn g with
    hgB | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact hgB
  · rw [MulAction.mem_stabilizer_iff] at hg
    rcases hb₁ with ⟨x, rfl⟩
    have hb₂fix : b₂ • Unital.infinity n = Unital.infinity n :=
      MulAction.mem_stabilizer_iff.mp
        (standardBorel_le_infinityStabilizer hb₂)
    rw [mul_smul, mul_smul, hb₂fix, weylElement_smul_infinity] at hg
    have haffine : Unital.affine x.left = Unital.infinity n := by
      simpa only [borelHom_smul_origin] using hg
    exact (Unital.affine_ne_infinity x.left haffine).elim

/-- As a consequence of the two-cell decomposition and stabilizer
identification, the exact order of the standard projective unitary permutation
group. -/
theorem natCard_standardPermGroup (n : ℕ) (hn : 0 < n) :
    Nat.card (standardPermGroup n) =
      2 ^ (3 * n) * (2 ^ (3 * n) + 1) *
        ((2 ^ (2 * n) - 1) / (2 ^ n + 1).gcd 3) := by
  letI : MulAction.IsPretransitive (standardPermGroup n) (Unital n) :=
    standardPermGroup_isPretransitive n
  have hindex := MulAction.index_stabilizer_of_transitive
    (standardPermGroup n) (Unital.infinity n)
  rw [← standardBorel_eq_infinityStabilizer n hn,
    Unital.natCard n hn] at hindex
  calc
    Nat.card (standardPermGroup n) =
        Nat.card (standardBorel n) * (standardBorel n).index :=
      (standardBorel n).card_mul_index.symm
    _ = 2 ^ (3 * n) *
          ((2 ^ (2 * n) - 1) / (2 ^ n + 1).gcd 3) *
            (2 ^ (3 * n) + 1) := by
      rw [natCard_standardBorel n hn, hindex]
    _ = _ := by ac_rfl

end


end


end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
