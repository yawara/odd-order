/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiEndgame
import OddOrder.GroupTheory.CardSupInf

/-!
# Brauer–Suzuki: the `Q₈` case (Navarro, *Characters and Blocks*, pp. 139–146)

The `|S| ≥ 16` branch of Brauer–Suzuki is `brauerSuzuki_of_quaternionSylow`, proved by ordinary
exceptional characters (Gorenstein Ch. 12).  For `S ≅ Q₈` that argument breaks down and modular
character theory is genuinely required; Navarro's proof (pp. 139–146) is the spine being
formalised in issue 9506, on top of the Brauer-character/block machinery of
`GroupTheory/RepresentationTheory/Modular/`.

This file isolates **what is still missing**.  Two reductions are done here, leaving exactly
Navarro's own statement:

* the group-theoretic endgame is shared with the `|S| ≥ 16` branch and already proved
  (`oPiCore_sup_centralizer_eq_top_of_mk_mem_center`): once the image of the involution is central
  modulo `O_{2'}(G)`, the conclusion `G = O_{2'}(G)·C_G(z)` follows;
* the passage to `Ḡ = G/O_{2'}(G)` (`q8_mk_mem_center`) is legitimate because `O_{2'}(Ḡ) = 1` and
  the Sylow `2`-subgroups of `Ḡ` are again `Q₈` — the odd core meets `T` trivially
  (`sylowTwo_inf_oPiCore_eq_bot`).

So the whole content of the `Q₈` case is `q8_mem_center_of_oPiCore_eq_bot`, which is verbatim
Navarro's "it suffices to prove that `t ∈ Z(G)`" under `O_{2'}(G) = 1`.

## Main results

* `OddOrder.GroupTheory.q8_mem_center_of_oPiCore_eq_bot` — **the remaining mathematics**
  (issue 9506, `sorry`)
* `OddOrder.GroupTheory.mem_center_of_normal_of_isCyclic` — how both branches of Navarro's
  reduction on p. 139 finish
* `OddOrder.GroupTheory.q8_mk_mem_center` / `OddOrder.GroupTheory.brauerSuzuki_q8`
-/

open OddOrder.Isaacs.Ch03

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- **The odd core meets a Sylow `2`-subgroup trivially**: the intersection has order dividing
both a power of `2` and an odd number. -/
theorem sylowTwo_inf_oPiCore_eq_bot (T : Sylow 2 G) :
    (T : Subgroup G) ⊓ oPiCore {p | p ≠ 2} G = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKodd : ¬ 2 ∣ Nat.card ↥(oPiCore {p | p ≠ 2} G) := fun h2 =>
    (oPiCore.isPiGroup {p | p ≠ 2}) 2
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, Nat.card_pos.ne'⟩) rfl
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hdvdT : Nat.card ↥((T : Subgroup G) ⊓ oPiCore {p | p ≠ 2} G) ∣ 2 ^ n := by
    rw [← hn]; exact card_dvd_card_of_le inf_le_left
  have hdvdK : Nat.card ↥((T : Subgroup G) ⊓ oPiCore {p | p ≠ 2} G)
      ∣ Nat.card ↥(oPiCore {p | p ≠ 2} G) := card_dvd_card_of_le inf_le_right
  refine Subgroup.card_eq_one.mp ?_
  by_contra hne
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdT
  have hj0 : j ≠ 0 := fun h => hne (by rw [hj, h, pow_zero])
  exact hKodd (((hj ▸ dvd_pow_self 2 hj0)).trans hdvdK)

/-- **An involution of a normal cyclic subgroup is central.**  Conjugates of `z` stay in `N` and
are again involutions, and a cyclic group has at most one involution
(`eq_of_sq_eq_one_of_isCyclic`).

This is how *both* branches of Navarro's reduction (p. 139) finish: either `N` itself is a cyclic
`2`-group, or `Z(N) = ⟨t⟩`. -/
theorem mem_center_of_normal_of_isCyclic {N : Subgroup G} [N.Normal] [IsCyclic ↥N] {z : G}
    (hzN : z ∈ N) (hz : orderOf z = 2) : z ∈ Subgroup.center G := by
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hconjN : g * z * g⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹N.Normal› z hzN g
  have hconj_sq : (g * z * g⁻¹) ^ 2 = 1 := by
    rw [show g * z * g⁻¹ = MulAut.conj g z from rfl, ← map_pow, hz2, map_one]
  have hconj_ne : g * z * g⁻¹ ≠ 1 := fun h =>
    hz1 ((MulAut.conj g).injective (h.trans (map_one (MulAut.conj g)).symm))
  have hkey := eq_of_sq_eq_one_of_isCyclic (C := ↥N)
    (a := ⟨g * z * g⁻¹, hconjN⟩) (b := ⟨z, hzN⟩)
    (Subtype.ext (by push_cast; exact hconj_sq)) (by simpa using hconj_ne)
    (Subtype.ext (by push_cast; exact hz2)) (by simpa using hz1)
  have hgz : g * z * g⁻¹ = z := congrArg Subtype.val hkey
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [hgz]

/-- **Brauer–Suzuki for `Q₈`, the residual statement** (Navarro pp. 139–146; issue 9506): with
`O_{2'}(G) = 1`, the involution of a quaternion Sylow `2`-subgroup of order `8` is central.

The proof is the eight pages pp. 139–146: a unique `G`-class of elements of order `4` (fusion
control plus `Aut(Q₈) = Sym(4)`), then the "analysis at `y`" and "analysis at `t`" with the
principal-block basic set of Navarro (7.3)/(7.4) — for which the integral change-of-basis matrix
`intBasicSetMatrix` (issue 9508, closed) is the prerequisite — producing a nontrivial character of
`B₀` with `t` in its kernel. -/
theorem q8_mem_center_of_oPiCore_eq_bot (hO : oPiCore {p | p ≠ 2} G = ⊥) (T : Sylow 2 G)
    (hq : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup 2))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    z ∈ Subgroup.center G := by
  sorry

/-- **Brauer–Suzuki for `Q₈`, in the form the endgame consumes**: the image of the involution is
central modulo the odd core.

This is `q8_mem_center_of_oPiCore_eq_bot` applied to `Ḡ = G/O_{2'}(G)`, which is legitimate
because `O_{2'}(Ḡ) = 1` (`oPiCore_quotient_self_eq_bot`) and the Sylow `2`-subgroups of `Ḡ` are
again `Q₈`: the odd core meets `T` trivially (`sylowTwo_inf_oPiCore_eq_bot`), so `T → Ḡ` is
injective and its image — a Sylow `2`-subgroup of `Ḡ` by `Sylow.mapSurjective` — is isomorphic
to `T`. -/
theorem q8_mk_mem_center (T : Sylow 2 G)
    (hq : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup 2))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    QuotientGroup.mk' (oPiCore {p | p ≠ 2} G) z
      ∈ Subgroup.center (G ⧸ oPiCore {p | p ≠ 2} G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oPiCore {p | p ≠ 2} G with hK
  set q := QuotientGroup.mk' K with hq'
  -- `T → Ḡ` is injective, since `T ⊓ K = ⊥`
  set f : ↥(T : Subgroup G) →* G ⧸ K := q.comp (T : Subgroup G).subtype with hf
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, ha⟩ hafx
    have haK : a ∈ K := (QuotientGroup.eq_one_iff a).mp hafx
    have : a ∈ (T : Subgroup G) ⊓ K := ⟨ha, haK⟩
    rw [sylowTwo_inf_oPiCore_eq_bot T, Subgroup.mem_bot] at this
    exact Subtype.ext this
  -- the image is a Sylow `2`-subgroup of `Ḡ`, isomorphic to `T`
  have hrange : f.range = (T : Subgroup G).map q := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e⟩ := hq
  refine q8_mem_center_of_oPiCore_eq_bot (oPiCore_quotient_self_eq_bot {p | p ≠ 2})
    (T.mapSurjective (QuotientGroup.mk'_surjective K))
    ⟨((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hfinj).symm).trans e⟩
    (Subgroup.mem_map_of_mem _ hzT) ?_
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, hz2, map_one]
  · rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact notMem_oPiCore_of_orderOf_eq_two hz

/-- **Brauer–Suzuki, the `Q₈` case.**  The group-theoretic endgame
(`oPiCore_sup_centralizer_eq_top_of_mk_mem_center`) applied to `q8_mk_mem_center`. -/
theorem brauerSuzuki_q8 (T : Sylow 2 G) (hq : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup 2))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    oPiCore {p | p ≠ 2} G ⊔ Subgroup.centralizer {z} = ⊤ :=
  oPiCore_sup_centralizer_eq_top_of_mk_mem_center hz (q8_mk_mem_center T hq hzT hz)

end OddOrder.GroupTheory
