/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiEndgame

/-!
# Brauer–Suzuki: the `Q₈` case (Navarro, *Characters and Blocks*, pp. 139–146)

The `|S| ≥ 16` branch of Brauer–Suzuki is `brauerSuzuki_of_quaternionSylow`, proved by ordinary
exceptional characters (Gorenstein Ch. 12).  For `S ≅ Q₈` that argument breaks down and modular
character theory is genuinely required; Navarro's proof (pp. 139–146) is the spine being
formalised in issue 9506, on top of the Brauer-character/block machinery of
`GroupTheory/RepresentationTheory/Modular/`.

This file isolates **what is still missing**.  The group-theoretic endgame is shared with the
`|S| ≥ 16` branch and already proved
(`oPiCore_sup_centralizer_eq_top_of_mk_mem_center`): once the image of the involution is central
modulo `O_{2'}(G)`, the conclusion `G = O_{2'}(G)·C_G(z)` follows.  So the whole content of the
`Q₈` case is the single statement `q8_mk_mem_center` below, which is exactly Navarro's
"it suffices to prove that `t ∈ Z(G)`" after passing to `Ḡ = G/O_{2'}(G)`.

## Main results

* `OddOrder.GroupTheory.q8_mk_mem_center` — **the remaining mathematics** (issue 9506, `sorry`)
* `OddOrder.GroupTheory.brauerSuzuki_q8` — the `Q₈` case, modulo the above
-/

open OddOrder.Isaacs.Ch03

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- **Brauer–Suzuki for `Q₈`, the residual statement** (Navarro pp. 139–146; issue 9506): the
image of the involution `z` of a quaternion Sylow `2`-subgroup of order `8` is central in
`Ḡ = G/O_{2'}(G)`.

Navarro proves this as `t ∈ Z(G)` under `O_{2'}(G) = 1`; the general form is that statement
applied to `Ḡ`, whose odd core is trivial and whose Sylow `2`-subgroups are again `Q₈` (the odd
core meets a Sylow `2`-subgroup trivially).

The proof is the eight pages pp. 139–146: a unique `G`-class of elements of order `4` (fusion
control plus `Aut(Q₈) = Sym(4)`), then the "analysis at `y`" and "analysis at `t`" with the
principal-block basic set of Navarro (7.3)/(7.4) — for which the integral change-of-basis matrix
`intBasicSetMatrix` (issue 9508, closed) is the prerequisite — producing a nontrivial character of
`B₀` with `t` in its kernel. -/
theorem q8_mk_mem_center (T : Sylow 2 G)
    (hq : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup 2))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    QuotientGroup.mk' (oPiCore {p | p ≠ 2} G) z
      ∈ Subgroup.center (G ⧸ oPiCore {p | p ≠ 2} G) := by
  sorry

/-- **Brauer–Suzuki, the `Q₈` case.**  The group-theoretic endgame
(`oPiCore_sup_centralizer_eq_top_of_mk_mem_center`) applied to `q8_mk_mem_center`. -/
theorem brauerSuzuki_q8 (T : Sylow 2 G) (hq : Nonempty (↥(T : Subgroup G) ≃* QuaternionGroup 2))
    {z : G} (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2) :
    oPiCore {p | p ≠ 2} G ⊔ Subgroup.centralizer {z} = ⊤ :=
  oPiCore_sup_centralizer_eq_top_of_mk_mem_center hz (q8_mk_mem_center T hq hzT hz)

end OddOrder.GroupTheory
