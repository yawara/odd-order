/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CenterSimplesOrbit
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03

/-!
# A coprime fixed-point-free automorphism fixes only the trivial conjugacy class

For Peterfalvi (9.1)'s kernel-FPF count (†) (step 3d.2), we need that a Frobenius-complement element
`e`, acting by conjugation on the kernel `U`, fixes only the trivial conjugacy class — equivalently,
`⟨e⟩` acts *freely* on the nontrivial classes.  The orbit-count Brauer equality
(`CenterSimplesOrbit.card_orbits_classes_eq_card_orbits_simples_comp`) then transfers this to the
simples, which feeds the free-action dimension count (I-3) to give (†).

This file proves the group-theoretic crux:

`map_eq_self_imp_eq_trivial_of_fpf` — if `β : MulAut G` generates a cyclic group of order coprime
to `|G|` and acts without nonidentity fixed points (`β x = x → x = 1`), then any `β`-fixed
conjugacy class is the trivial class `mk 1`.

The proof realises the class `C` as a transitive `G`-conjugation set `Ω = {y // mk y = C}`, on which
`⟨β⟩` acts compatibly via `β`; **Glauberman's fixed-point lemma** (Isaacs 3.24(a),
`OddOrder.Isaacs.Ch04.glauberman_fixed_point_exists`) produces a `β`-fixed element of `C`, which
lies in `Fix(β) = {1}`, forcing `C = mk 1`.  No characteristic-0 / Brauer-character input.
-/

open OddOrder.Isaacs.Ch04 (glauberman_fixed_point_exists IsCompatibleMulAction)
open OddOrder.GroupTheory.CenterClassSum

namespace OddOrder.GroupTheory.CenterOrbitFree

variable {G : Type*} [Group G] [Finite G]

/-- **A coprime fixed-point-free automorphism fixes only the trivial conjugacy class.**
If `β : MulAut G` generates a cyclic group of order coprime to `|G|` (`hCop`) and acts without
nonidentity fixed points (`hFPF : β x = x → x = 1`), then any `β`-fixed conjugacy class `C`
(`hC : β • C = C`) is the trivial class `mk 1`.

Proof: the cyclic group `A = ⟨β⟩` acts on `C` realised as the transitive `G`-conjugation set
`Ω = {y // mk y = C}`, compatibly with conjugation (`β(g y g⁻¹) = β g · β y · (β g)⁻¹`).  Glauberman
(Isaacs 3.24(a)) yields a `β`-fixed element `y ∈ C`; `β y = y` and `hFPF` give `y = 1`, so
`C = mk y = mk 1`. -/
theorem map_eq_self_imp_eq_trivial_of_fpf (β : MulAut G)
    (hCop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers β)) (Nat.card G))
    (hFPF : ∀ x : G, β x = x → x = 1)
    {C : ConjClasses G} (hC : β • C = C) :
    C = ConjClasses.mk 1 := by
  classical
  -- The acting cyclic group `A = ⟨β⟩` and its inclusion `φ` into `MulAut G`.
  let φ : ↥(Subgroup.zpowers β) →* MulAut G := (Subgroup.zpowers β).subtype
  -- Every element of `⟨β⟩` fixes `C`: the stabiliser is a subgroup containing `β`.
  have hAfix : ∀ a : ↥(Subgroup.zpowers β), (φ a) • C = C := fun a =>
    MulAction.mem_stabilizer_iff.mp
      (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hC) a.2)
  -- `Ω` := the class `C` as a subtype, nonempty (it has a representative).
  obtain ⟨x₀, hx₀⟩ := ConjClasses.mk_surjective C
  let Ω := {y : G // ConjClasses.mk y = C}
  haveI : Nonempty Ω := ⟨⟨x₀, hx₀⟩⟩
  -- `G` acts on `Ω` by conjugation (class-preserving).
  letI mulG : MulAction G Ω := {
    smul := fun g y => ⟨g * y.1 * g⁻¹,
      (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by group⟩)).trans y.2⟩
    one_smul := fun y => Subtype.ext (by change (1 : G) * y.1 * (1 : G)⁻¹ = y.1; group)
    mul_smul := fun g g' y =>
      Subtype.ext (by change (g * g') * y.1 * (g * g')⁻¹ = g * (g' * y.1 * g'⁻¹) * g⁻¹; group) }
  -- `A = ⟨β⟩` acts on `Ω` via `φ` (well-defined since every `a ∈ ⟨β⟩` fixes `C`).
  letI mulA : MulAction (↥(Subgroup.zpowers β)) Ω := {
    smul := fun a y => ⟨(φ a) y.1, by rw [← mulAut_smul_mk, y.2, hAfix a]⟩
    one_smul := fun y => Subtype.ext (by change (φ 1) y.1 = y.1; simp)
    mul_smul := fun a b y =>
      Subtype.ext (by change (φ (a * b)) y.1 = (φ a) ((φ b) y.1); simp [map_mul]) }
  -- Conjugation and the `φ`-action are compatible.
  have hCompat : IsCompatibleMulAction φ Ω := by
    intro a g y
    apply Subtype.ext
    change (φ a) (g * y.1 * g⁻¹) = (φ a g) * ((φ a) y.1) * (φ a g)⁻¹
    rw [map_mul, map_mul, map_inv]
  -- `G` acts transitively on `Ω` (any two representatives of `C` are conjugate).
  have hG_trans : MulAction.IsPretransitive G Ω := by
    refine ⟨fun y z => ?_⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (y.2.trans z.2.symm))
    exact ⟨c, Subtype.ext hc⟩
  -- `⟨β⟩` is commutative, hence solvable (so Glauberman's solvability hypothesis holds).
  haveI : IsSolvable (↥(Subgroup.zpowers β)) := isSolvable_of_comm fun a b => mul_comm' a b
  -- Glauberman 3.24(a): a `⟨β⟩`-fixed element of `Ω` exists.
  obtain ⟨ω₀, hω₀⟩ := glauberman_fixed_point_exists (G := G) (A := ↥(Subgroup.zpowers β)) (φ := φ)
    hCop (Or.inl inferInstance) (Ω := Ω) hCompat hG_trans
  -- It is `β`-fixed, hence trivial by `hFPF`; so `C = mk 1`.
  have hβfix : β ω₀.1 = ω₀.1 := Subtype.ext_iff.mp (hω₀ ⟨β, Subgroup.mem_zpowers β⟩)
  rw [← ω₀.2, hFPF ω₀.1 hβfix]

end OddOrder.GroupTheory.CenterOrbitFree
