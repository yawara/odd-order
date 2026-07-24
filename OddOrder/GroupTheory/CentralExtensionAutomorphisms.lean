/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CentralElementaryExtension

/-!
# Isomorphisms of central elementary extensions along coordinate changes

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Lemma 1(c), pp. 139–140.

Let `1 → W → E → V → 1` and `1 → W' → E' → V' → 1` be central extensions of
elementary abelian `2`-groups with square maps `q : V → W` and
`q' : V' → W'`, and let `f : V ≃+ V'` and `g : W ≃+ W'` be isomorphisms.
Lemma 1(c) states that an isomorphism `E ≃* E'` inducing `f` on the
quotients and `g` on the kernels exists if and only if `g ∘ q = q' ∘ f`.

Necessity is immediate from the square-coordinate formulas.  For
sufficiency, transport the primed extension along `(f, g)` — keeping the
middle group `E'` and reindexing the two end groups
(`GroupExtension.twistCoords`) — so that both extensions become extensions
of `V` by `W` with the *same* square map `q`; then
`GroupExtension.equivOfCommonSquareMap` produces the equivalence.

Main declarations:

* `GroupExtension.twistCoords` — reindex the end groups of an extension
  along isomorphisms, keeping the middle group;
* `GroupExtension.comp_squareMap_eq_of_mulEquiv` — Lemma 1(c), necessity;
* `GroupExtension.exists_mulEquiv_of_comp_squareMap_eq` — Lemma 1(c),
  sufficiency.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

noncomputable section

universe uV uW uV' uW' uE uE'

section Twist

variable {K : Type uW} [Group K] {K' : Type uW'} [Group K']
variable {Q : Type uV} [Group Q] {Q' : Type uV'} [Group Q']
variable {E : Type uE} [Group E]

/-- Reindex the two end groups of an extension along isomorphisms, keeping
the middle group. -/
def _root_.GroupExtension.twistCoords (S : GroupExtension K E Q)
    (gK : K' ≃* K) (gQ : Q ≃* Q') : GroupExtension K' E Q' where
  inl := S.inl.comp gK.toMonoidHom
  rightHom := gQ.toMonoidHom.comp S.rightHom
  inl_injective := S.inl_injective.comp gK.injective
  range_inl_eq_ker_rightHom := by
    ext e
    simp only [MonoidHom.mem_range, MonoidHom.mem_ker, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨k, rfl⟩
      have hk : S.inl (gK k) ∈ S.rightHom.ker :=
        S.range_inl_eq_ker_rightHom ▸ ⟨gK k, rfl⟩
      rw [MonoidHom.mem_ker] at hk
      rw [hk, map_one]
    · intro he
      have h1 : S.rightHom e = 1 := gQ.injective (by rw [he, map_one])
      have : e ∈ S.inl.range :=
        S.range_inl_eq_ker_rightHom ▸ MonoidHom.mem_ker.mpr h1
      obtain ⟨k, rfl⟩ := this
      exact ⟨gK.symm k, by simp⟩
  rightHom_surjective := gQ.surjective.comp S.rightHom_surjective

@[simp]
theorem _root_.GroupExtension.twistCoords_inl (S : GroupExtension K E Q)
    (gK : K' ≃* K) (gQ : Q ≃* Q') (k : K') :
    (S.twistCoords gK gQ).inl k = S.inl (gK k) :=
  rfl

@[simp]
theorem _root_.GroupExtension.twistCoords_rightHom (S : GroupExtension K E Q)
    (gK : K' ≃* K) (gQ : Q ≃* Q') (e : E) :
    (S.twistCoords gK gQ).rightHom e = gQ (S.rightHom e) :=
  rfl

end Twist

section LemmaOneC

variable {V : Type uV} [AddCommGroup V]
variable {W : Type uW} [AddCommGroup W]
variable {V' : Type uV'} [AddCommGroup V']
variable {W' : Type uW'} [AddCommGroup W']
variable {E : Type uE} [Group E] {E' : Type uE'} [Group E']

/-- **Peterfalvi Appendix III, Lemma 1(c), necessity** (p. 139): if an
isomorphism of central extensions induces `f` on the quotients and `g` on
the kernels, then the square maps are intertwined: `g ∘ q = q' ∘ f`. -/
theorem _root_.GroupExtension.comp_squareMap_eq_of_mulEquiv
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (T : GroupExtension (Multiplicative W') E' (Multiplicative V'))
    (q : V → W) (q' : V' → W')
    (hsqS : ∀ e : E,
      e ^ 2 = S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (hsqT : ∀ e : E',
      e ^ 2 = T.inl (Multiplicative.ofAdd (q' (T.rightHom e).toAdd)))
    (f : V → V') (g : W → W') (Φ : E ≃* E')
    (hinl : ∀ w : W,
      Φ (S.inl (Multiplicative.ofAdd w)) = T.inl (Multiplicative.ofAdd (g w)))
    (hright : ∀ e : E, (T.rightHom (Φ e)).toAdd = f (S.rightHom e).toAdd)
    (v : V) : g (q v) = q' (f v) := by
  obtain ⟨e, he⟩ := S.rightHom_surjective (Multiplicative.ofAdd v)
  have hsq : Φ (e ^ 2) = Φ e ^ 2 := map_pow Φ e 2
  rw [hsqS e, hsqT (Φ e), he, toAdd_ofAdd, hinl] at hsq
  have hcoord := T.inl_injective hsq
  have hW := congrArg (fun z : Multiplicative W' => z.toAdd) hcoord
  simp only [toAdd_ofAdd] at hW
  rw [hW, hright, he, toAdd_ofAdd]

/-- **Peterfalvi Appendix III, Lemma 1(c), sufficiency** (p. 140): given
central extensions of elementary abelian `2`-groups with square maps `q`,
`q'` and isomorphisms `f`, `g` with `g ∘ q = q' ∘ f`, there is an
isomorphism of the middle groups inducing `f` on the quotients and `g` on
the kernels. -/
theorem _root_.GroupExtension.exists_mulEquiv_of_comp_squareMap_eq {n : ℕ}
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    (S : GroupExtension (Multiplicative W) E (Multiplicative V))
    (T : GroupExtension (Multiplicative W') E' (Multiplicative V'))
    (hcentralS : S.inl.range ≤ Subgroup.center E)
    (hcentralT : T.inl.range ≤ Subgroup.center E')
    (q : V → W) (q' : V' → W')
    (basis : Module.Basis (Fin n) (ZMod 2) V)
    (hsqS : ∀ e : E,
      e ^ 2 = S.inl (Multiplicative.ofAdd (q (S.rightHom e).toAdd)))
    (hsqT : ∀ e : E',
      e ^ 2 = T.inl (Multiplicative.ofAdd (q' (T.rightHom e).toAdd)))
    (f : V ≃+ V') (g : W ≃+ W')
    (hcomp : ∀ v : V, g (q v) = q' (f v)) :
    ∃ Φ : E ≃* E',
      (∀ w : W, Φ (S.inl (Multiplicative.ofAdd w)) =
        T.inl (Multiplicative.ofAdd (g w))) ∧
      ∀ e : E, (T.rightHom (Φ e)).toAdd = f (S.rightHom e).toAdd := by
  -- Transport `T` to an extension of `V` by `W` with square map `q`.
  set T' : GroupExtension (Multiplicative W) E' (Multiplicative V) :=
    T.twistCoords (AddEquiv.toMultiplicative g)
      (AddEquiv.toMultiplicative f.symm) with hT'
  have hcentralT' : T'.inl.range ≤ Subgroup.center E' := by
    rintro x ⟨k, rfl⟩
    exact hcentralT ⟨AddEquiv.toMultiplicative g k, rfl⟩
  have hsqT' : ∀ e : E',
      e ^ 2 = T'.inl (Multiplicative.ofAdd (q (T'.rightHom e).toAdd)) := by
    intro e
    rw [hsqT e]
    have hval : g (q (f.symm (T.rightHom e).toAdd)) =
        q' (T.rightHom e).toAdd := by
      have := hcomp (f.symm (T.rightHom e).toAdd)
      rwa [f.apply_symm_apply] at this
    change T.inl (Multiplicative.ofAdd (q' (T.rightHom e).toAdd)) =
      T.inl (Multiplicative.ofAdd (g (q (f.symm (T.rightHom e).toAdd))))
    rw [hval]
  let equiv := GroupExtension.equivOfCommonSquareMap S T' hcentralS
    hcentralT' q basis hsqS hsqT'
  refine ⟨equiv.toMulEquiv, ?_, ?_⟩
  · intro w
    exact congrFun equiv.inl_comm (Multiplicative.ofAdd w)
  · intro e
    have h1 := congrFun equiv.rightHom_comm e
    have h2 : f.symm (T.rightHom (equiv.toMulEquiv e)).toAdd =
        (S.rightHom e).toAdd :=
      congrArg (fun z : Multiplicative V => z.toAdd) h1
    rw [← h2, f.apply_symm_apply]

end LemmaOneC

end

end OddOrder.GroupTheory
