import OddOrder.BG.Ch1_Preliminary.S03g_Thm310Module
import OddOrder.Isaacs.Ch02_Subnormality.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# BG Theorem 3.10, general (non-abelian) kernel — the K₀ reduction (issue 8013, piece 3)

The abelian-kernel forms of BG Theorem 3.10 (`prime_card_and_finrank_of_abelian_frobenius_weight`,
`prime_card_and_finrank_of_elemAbelian`) cover conclusions (a) `|R|` prime and (b)
`finrank V = |R| · finrank C_V(R)` when the Frobenius kernel `K` is **abelian**.  The §15.2
application (Theorem 15.2 step 4, issue 8012) needs a **general** kernel `D` (possibly non-abelian).

BG handles this by the **`K₀` reduction** (Case 2 of the Theorem 3.10 proof, mmd L1340-1349): in the
irreducible-module case, an induction on `|K|` reduces a general kernel to a minimal-normal (hence
elementary abelian, hence abelian) one.  Pick `K₀ ⊴ G` minimal normal with `K₀ ⊆ K`.  As `K₀ ⊴ G`
and `V` is irreducible, `C_V(K₀)` is `⊥` or `⊤` (the dichotomy below).
* If `C_V(K₀) = ⊥`: the Frobenius configuration with kernel `K₀` (smaller) satisfies all hypotheses,
  so the induction hypothesis applies directly (same `G`, `V`, `R`) — Case A.
* If `C_V(K₀) = ⊤`: `K₀` acts trivially on `V`, so `ρ` factors through `G/K₀`, where the kernel is
  `K/K₀` (smaller); the induction hypothesis applies to the quotient — Case B (heavy).
The base case `K₀ = K` (i.e. `K` minimal normal) is the abelian-kernel theorem.

This file builds that reduction.  **Status (issue 8013 piece 3)**: the irreducibility dichotomy is
landed here; the induction (base + Case A + Case B quotient) is the remaining frontier.
-/

namespace OddOrder.BG.Ch1.S03

open Module

variable {F : Type*} [Field F] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- **Irreducible ⟹ the invariants of a normal subgroup are `⊥` or `⊤`** (the dichotomy driving the
`K₀` reduction of BG Theorem 3.10, Case 2; mmd L1342 "since `C_M(K₀)` is a `G`-invariant subgroup of
`M`, either `C_M(K₀)=1` or `C_M(K₀)=M`").  For an irreducible representation `ρ` and a normal
subgroup `K₀ ⊴ G`, the `K₀`-invariants `C_V(K₀) = invariants (ρ.comp K₀.subtype)` form a
`G`-invariant submodule (because `K₀` is normal: `ρ g` carries a `K₀`-fixed vector to a `K₀`-fixed
vector, conjugating the fixing element back into `K₀`), hence a subrepresentation, which an
irreducible `ρ` forces to be `⊥` or `⊤`. -/
theorem invariants_normal_eq_bot_or_top_of_isIrreducible
    (ρ : Representation F G V) [ρ.IsIrreducible]
    {K₀ : Subgroup G} [hK₀ : K₀.Normal] :
    Representation.invariants (ρ.comp K₀.subtype) = ⊥ ∨
      Representation.invariants (ρ.comp K₀.subtype) = ⊤ := by
  -- Package `C_V(K₀)` as a subrepresentation (it is `G`-invariant because `K₀ ⊴ G`).
  set S : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants (ρ.comp K₀.subtype)
      apply_mem_toSubmodule := by
        intro g v hv
        rw [Representation.mem_invariants] at hv ⊢
        intro k₀
        -- `ρ k₀ (ρ g v) = ρ (k₀ * g) v = ρ (g * (g⁻¹ k₀ g)) v = ρ g (ρ (g⁻¹ k₀ g) v) = ρ g v`.
        have hconj : g⁻¹ * (k₀ : G) * g ∈ K₀ := by
          have := hK₀.conj_mem (k₀ : G) k₀.2 g⁻¹
          simpa using this
        have hfix := hv ⟨g⁻¹ * (k₀ : G) * g, hconj⟩
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hfix ⊢
        rw [← Module.End.mul_apply, ← map_mul]
        have hgg : (k₀ : G) * g = g * (g⁻¹ * (k₀ : G) * g) := by group
        rw [hgg, map_mul, Module.End.mul_apply, hfix] } with hS
  -- An irreducible representation has only `⊥` and `⊤` as subrepresentations.
  rcases IsSimpleOrder.eq_bot_or_eq_top S with hb | ht
  · left
    have h := congrArg Subrepresentation.toSubmodule hb
    simpa using h
  · right
    have h := congrArg Subrepresentation.toSubmodule ht
    simpa using h

/-- **BG Theorem 3.10(a)+(b), the induction base case** (mmd L1346 "we can assume that `K` is a
minimal normal subgroup of `KR`; since `KR` is solvable, this implies that `K` is an elementary
abelian `q`-group").  When the Frobenius kernel `K` is minimal normal in the (solvable) group `G`,
it is elementary abelian (`solvable_minimal_normal_isElementaryAbelian`), in particular abelian, so
the abelian-kernel rank theorem `prime_card_and_finrank_of_abelian_frobenius_weight` applies and
yields (a) `|R|` prime and (b) `finrank V = |R| · finrank C_V(R)`.

This is the base of the `K₀`-reduction induction (issue 8013 piece 3): the recursive step reduces a
general kernel to this case via `invariants_normal_eq_bot_or_top_of_isIrreducible`. -/
theorem prime_card_and_finrank_of_minimalNormal_kernel [Finite G] [IsAlgClosed F] [IsSolvable G]
    (ρ : Representation F G V) [FiniteDimensional F V] [Nontrivial V]
    {K R : Subgroup G} [K.Normal] (hRne : R ≠ ⊥)
    (hKmin : OddOrder.Isaacs.Ch02.IsMinimalNormal K)
    (hKcard : (Nat.card ↥K : F) ≠ 0)
    (hCVK : Representation.invariants (ρ.comp K.subtype) = ⊥)
    (hFrob : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k)
    (hcond3 : ∀ x : G, x ∈ R → x ≠ 1 →
      finrank F (Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype))
        = finrank F (Representation.invariants (ρ.comp R.subtype))) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p ∧
      finrank F V = Nat.card ↥R * finrank F (Representation.invariants (ρ.comp R.subtype)) := by
  obtain ⟨q, _hq, hKea⟩ := OddOrder.Isaacs.Ch03.solvable_minimal_normal_isElementaryAbelian hKmin
  have hKab : ∀ a b : ↥K, (a : G) * (b : G) = (b : G) * (a : G) := by
    intro a b
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hKea.comm]
  exact prime_card_and_finrank_of_abelian_frobenius_weight ρ hRne hKab hKcard hCVK hFrob hcond3

/-- **Case B transfer brick — invariants are preserved under the lift to `G ⧸ K₀`** (issue 8013
piece 3).  When `K₀` acts trivially (`ρ x = 1` for `x ∈ K₀`), `ρ` factors as
`ρ̄ = QuotientGroup.lift K₀ ρ` through `G ⧸ K₀`, and the `ρ̄`-invariants of the image `S·K₀/K₀` of any
`S ≤ G` coincide (as a submodule of `V`) with the `ρ`-invariants of `S`: the actions agree on
representatives (`ρ̄ ⟦g⟧ = ρ g`), so the same vectors are fixed.

In Case B of the `K₀` reduction this both transfers the hypothesis `C_V(K) = ⊥` to the quotient
(`S = K`) and transfers the conclusion's `C_V(R)` back from the quotient (`S = R`). -/
theorem invariants_lift_map_eq_of_trivial (ρ : Representation F G V) {K₀ : Subgroup G} [K₀.Normal]
    (hker : ∀ x ∈ K₀, ρ x = 1) (S : Subgroup G) :
    Representation.invariants
        ((QuotientGroup.lift K₀ ρ hker).comp (S.map (QuotientGroup.mk' K₀)).subtype)
      = Representation.invariants (ρ.comp S.subtype) := by
  ext v
  rw [Representation.mem_invariants, Representation.mem_invariants]
  constructor
  · intro h s
    have hmem : (QuotientGroup.mk' K₀) (s : G) ∈ S.map (QuotientGroup.mk' K₀) :=
      Subgroup.mem_map_of_mem _ s.2
    have hs := h ⟨(QuotientGroup.mk' K₀) (s : G), hmem⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.lift_mk'] at hs ⊢
    exact hs
  · intro h s'
    obtain ⟨g, hgS, hgeq⟩ := s'.2
    have hg := h ⟨g, hgS⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hg
    have hX : (S.map (QuotientGroup.mk' K₀)).subtype s' = (QuotientGroup.mk' K₀) g := hgeq.symm
    rw [MonoidHom.comp_apply, hX]
    exact hg

/-- **Case B transfer brick — the complement's order is unchanged by the lift** (issue 8013 piece 3).
A Frobenius complement `R` meets the kernel trivially (`R ∩ K₀ = ⊥`, here `K₀ ⊆ K`), so the quotient
map `mk' K₀` is injective on `R` and `|R·K₀/K₀| = |R|`.  Used to transfer `|R'| = p` (the quotient
conclusion (a)) back to `|R| = p`. -/
theorem card_map_mk'_eq_of_disjoint {K₀ R : Subgroup G} [K₀.Normal] (hdisj : Disjoint R K₀) :
    Nat.card (R.map (QuotientGroup.mk' K₀)) = Nat.card ↥R := by
  have hinj : Function.Injective ((QuotientGroup.mk' K₀).comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hr
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.disjoint_def.mp hdisj r.2 hr)
  have hrange : ((QuotientGroup.mk' K₀).comp R.subtype).range = R.map (QuotientGroup.mk' K₀) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

/-- **Case B transfer of BG Theorem 3.10 (a)+(b)** (issue 8013 piece 3): when `K₀` acts trivially,
the conclusion of the theorem for the lifted representation `ρ̄` on `G ⧸ K₀` (with kernel `K/K₀`,
complement `R·K₀/K₀`) transfers back to `ρ` on `G` (kernel `K`, complement `R`).  The complement's
order is unchanged (`card_map_mk'_eq_of_disjoint`) and so is the `finrank` of its invariants
(`invariants_lift_map_eq_of_trivial`), so `(a)` `|R| = p` and `(b)` `finrank V = |R| · finrank C_V(R)`
carry over verbatim.  The induction (Case B) supplies the quotient conclusion `hquot` by applying the
induction hypothesis to `ρ̄` (whose kernel `K/K₀` is strictly smaller). -/
theorem caseB_transfer (ρ : Representation F G V) {K₀ K R : Subgroup G} [K₀.Normal]
    (hker : ∀ x ∈ K₀, ρ x = 1) (hdisj : Disjoint R K₀)
    (hquot : ∃ p : ℕ, p.Prime ∧ Nat.card (R.map (QuotientGroup.mk' K₀)) = p ∧
      finrank F V = Nat.card (R.map (QuotientGroup.mk' K₀)) *
        finrank F (Representation.invariants
          ((QuotientGroup.lift K₀ ρ hker).comp (R.map (QuotientGroup.mk' K₀)).subtype))) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p ∧
      finrank F V = Nat.card ↥R * finrank F (Representation.invariants (ρ.comp R.subtype)) := by
  obtain ⟨p, hp, hcardR', hfinrank'⟩ := hquot
  have hcard : Nat.card (R.map (QuotientGroup.mk' K₀)) = Nat.card ↥R :=
    card_map_mk'_eq_of_disjoint hdisj
  have hinv : Representation.invariants
      ((QuotientGroup.lift K₀ ρ hker).comp (R.map (QuotientGroup.mk' K₀)).subtype)
      = Representation.invariants (ρ.comp R.subtype) :=
    invariants_lift_map_eq_of_trivial ρ hker R
  exact ⟨p, hp, by rw [← hcard]; exact hcardR', by rw [hfinrank', hcard, hinv]⟩

end OddOrder.BG.Ch1.S03
