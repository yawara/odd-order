/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.Main

/-!
# Peterfalvi Appendix B: transitivity implies irreducibility

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix B, Proposition 1, p. 135.

This lightweight leaf isolates the first implication of Proposition 1: an
action transitive on the nonidentity elements has no proper nontrivial
invariant subgroup.  It is used independently of the later Fitting and
fixed-point-free conclusions of the appendix.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Huppert

open OddOrder.Isaacs.Ch03

universe uD uE

variable {D : Type uD} {E : Type uE} [Group D] [Group E]

/-- **Peterfalvi Appendix B, Proposition 1 — irreducibility from
transitivity**: a group acting transitively on `E#` acts irreducibly, i.e.
every `D`-invariant subgroup of `E` is `bot` or `top`. -/
theorem isAInvariant_eq_bot_or_top_of_transitive
    (phi : D →* MulAut E)
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ g : D, (phi g) a = b)
    {U : Subgroup E} (hU : IsAInvariant phi U) : U = ⊥ ∨ U = ⊤ := by
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  · refine Or.inr (eq_top_iff.mpr fun b _ => ?_)
    rcases eq_or_ne b 1 with rfl | hb1
    · exact one_mem U
    · obtain ⟨a, haU, ha1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left h
      obtain ⟨g, hg⟩ := htrans a b ha1 hb1
      exact hg ▸ hU.smul_mem g haU

end OddOrder.Peterfalvi.Appendices.Huppert
