import OddOrder.GroupTheory.BrauerSuzukiSetup
import OddOrder.GroupTheory.SylowNormalRelIndex

/-!
# Brauer–Suzuki: the structure of `N = N_G(T)` (Gorenstein Ch. 12, Lemma 1.2)

**Gorenstein, *Finite Groups*, Ch. 12, Lemma 1.2** (p. 374): in the
`QuaternionSylowSetup` (issue 9318), with `T = ⟨x²⟩`, `C = C_G(T)`, `N = N_G(T)`:

(i) `N = SH` where `H ⊴ N` and `|H|` is odd; (ii) `C = XH`.

This file develops the proof along the book's lines:

* `C_le_N` / the `Normal` instance for `C.subgroupOf N` — `C ⊴ N`;
* `two_not_dvd_relIndex_C` — `X = S ∩ C` is a Sylow `2`-subgroup of `C` in index form
  (`2 ∤ [C : X]`), via `sylow_relIndex_normal_not_dvd` inside `N`;
* `exists_sylow_C_eq` — a bundled cyclic Sylow `2`-subgroup of `C` with carrier
  `X.subgroupOf C`.

The Burnside normal `2`-complement `H` of `C` and the assembly `N = SH`, `C = XH`
follow in the sequel.
-/

namespace OddOrder.GroupTheory

namespace QuaternionSylowSetup

open Subgroup

variable {G : Type*} [Group G] [Finite G] (Q : QuaternionSylowSetup G)

/-- `C = C_G(T) ≤ N_G(T) = N`. -/
theorem C_le_N : Q.C ≤ Q.N :=
  centralizer_le_normalizer (Q.T : Set G)

/-- **`C ⊴ N`** (Gorenstein p. 374): the centralizer is normal in the normalizer. -/
instance : (Q.C.subgroupOf Q.N).Normal :=
  normal_subgroupOf_centralizer_normalizer (Q.T : Set G)

/-- `X` is a `2`-group of order `2ⁿ`. -/
theorem card_X : Nat.card Q.X = 2 ^ Q.n := by
  rw [X, Nat.card_zpowers, Q.hx_order]

/-- **`X` is a Sylow `2`-subgroup of `C`, index form** (Gorenstein p. 374): the
relative index `[C : X]` is odd.  Obtained from `S ∩ C = X` and the
Sylow-intersect-normal lemma applied inside `N` (where `C` is normal). -/
theorem two_not_dvd_relIndex_C : ¬ 2 ∣ Q.X.relIndex Q.C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the Sylow-intersect-normal lemma inside `↥N`
  have h := sylow_relIndex_normal_not_dvd (Q.S.subtype Q.S_le_N) (Q.C.subgroupOf Q.N)
  rw [Sylow.coe_subtype, relIndex_subgroupOf Q.C_le_N] at h
  -- `[C : S] = [C : S ⊓ C] = [C : X]`
  rwa [← inf_relIndex_right, Q.S_inf_C_eq_X] at h

/-- `x ∈ C`. -/
theorem x_mem_C : Q.x ∈ Q.C :=
  Q.X_le_C (Q.mem_X_iff.mpr ⟨1, (zpow_one Q.x).symm⟩)

/-- **A cyclic Sylow `2`-subgroup of `C` with carrier `X`** (Gorenstein p. 374):
there is a Sylow `2`-subgroup of `C` equal to `X.subgroupOf C`; it is cyclic. -/
theorem exists_sylow_C_eq :
    ∃ P : Sylow 2 ↥Q.C, (P : Subgroup ↥Q.C) = Q.X.subgroupOf Q.C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `X.subgroupOf C` is a `2`-group…
  have hcard : Nat.card (Q.X.subgroupOf Q.C) = 2 ^ Q.n := by
    rw [Nat.card_congr (subgroupOfEquivOfLe Q.X_le_C).toEquiv, Q.card_X]
  have hp : IsPGroup 2 (Q.X.subgroupOf Q.C) := IsPGroup.of_card hcard
  -- …contained in some Sylow `2`-subgroup `P` of `C`.
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hP⟩
  -- `d = [P : X]` divides the odd `[C : X]` and the `2`-power `|P|`, hence `d = 1`.
  have hdvd_idx : (Q.X.subgroupOf Q.C).relIndex (P : Subgroup ↥Q.C) ∣ Q.X.relIndex Q.C :=
    ⟨(P : Subgroup ↥Q.C).index, (relIndex_mul_index hP).symm⟩
  have hodd : ¬ 2 ∣ (Q.X.subgroupOf Q.C).relIndex (P : Subgroup ↥Q.C) :=
    fun h => Q.two_not_dvd_relIndex_C (h.trans hdvd_idx)
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  have hdvd_card := relIndex_dvd_card (Q.X.subgroupOf Q.C) (P : Subgroup ↥Q.C)
  rw [hm] at hdvd_card
  obtain ⟨j, _, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_card
  have hj0 : j = 0 := by
    by_contra h
    exact hodd (hjeq ▸ dvd_pow_self 2 h)
  rw [hj0, pow_zero] at hjeq
  exact relIndex_eq_one.mp hjeq

end QuaternionSylowSetup

end OddOrder.GroupTheory
