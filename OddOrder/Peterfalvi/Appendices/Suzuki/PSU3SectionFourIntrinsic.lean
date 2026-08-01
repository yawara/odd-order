/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RankOneBNPairRigidity
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.Simplicity
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.Peterfalvi.Appendices.Suzuki.HypothesisFieldMatching
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourCorollaryTwo
import OddOrder.Peterfalvi.Appendices.Suzuki.RankOneSetup

/-!
# Ch. IV §4, step (2): the *intrinsic* standing hypothesis on `U/Z(U)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, step (2), p. 133.

`PSU3SectionFourModel` puts a standing hypothesis on `U/Z(U)` by *transporting* the
standard `PSU(3, ℓ)` one along Ch. I §3 Proposition 1(c).  Step (2) needs more than that:
it runs §2 and §3 "relative to `U`", with the mappings `f₁`, `h₁` of `U`, `U ∩ H` and `t`.
Those are the mappings of the rank-one setup `U/Z(U)` inherits from `U`
(`setup_residualQuotient`), so what step (2) really uses is the standing hypothesis whose
`H`, `Q`, `D`, `t` are the *images of the intrinsic subgroups* `U ∩ H`, `U ∩ Q`, `U ∩ D`
and `t`, not whatever the identification happens to produce.

`Hypothesis.ofRankOneSetup` builds exactly that from the setup, given faithfulness, `|Q̄|`
even, `|D̄|` odd and (A3).  This file supplies those four:

* faithfulness is `Setup.normalCore_eq_bot_of_isSimpleGroup`, because `U/Z(U)` is the
  simple group `PSU(3, ℓ)` (Ch. I §3 Lemma 1);
* `|Q̄| = |C_Q(X)|`, because `Z(U) ≤ D` meets `Q` trivially, so the quotient map is
  injective on `U ∩ Q = C_Q(X)`;
* `|D̄|` divides `|D|`, which is odd by (A2);
* (A3) is transported from the standard model — being a statement about the group alone,
  it does not care which identification is used.

The bridge `residualQuotientMulEquiv` is needed throughout because the model's
identification is stated for the residual as a subgroup of `C_G(X)` (`residual`) while the
setup lives on its image in `G` (`residualImage`).

## Main results

* `residualImageMulEquiv`, `residualQuotientMulEquiv` — `U` and `U/Z(U)` read in `G` agree
  with `U` and `U/Z(U)` read in `C_G(X)`.
* `isSimpleGroup_residualQuotient` — `U/Z(U)` is simple.
* `cQMulEquivMapQ`, `natCard_map_Q_residualQuotient` — `Q̄ ≃ C_Q(X)`, so `|Q̄| = |C_Q(X)|`.
* `odd_natCard_map_D_residualQuotient` — `|D̄|` is odd.
* `Hypothesis.intrinsicResidualQuotient` — the standing hypothesis on `U/Z(U)` in the
  intrinsic subgroups, which is what step (2) argues with.
* `natCard_Q0_intrinsicResidualQuotient`, `natCard_Q_intrinsicResidualQuotient`,
  `isSuzuki2Group_Q_intrinsicResidualQuotient` — the numerical and structural inputs of
  Ch. I §3 Lemma 5, for it.
* `intrinsicPointEquiv`, `intrinsicResidualQuotientULift` — the same hypothesis with its
  point set relabelled as the standard `Unital ℓ`, which lifts into `Ω`'s universe, and
  `theoremAInductionBelow_intrinsicResidualQuotient` — the induction hypothesis there.
* `exists_fgh_residual_eq`, `fgh_map_residualQuotient` — step (2)'s two transfers,
  `G ← U` (uniqueness of the canonical form) and `U ← U/Z(U)`.
* `rankOneSetup_centralizer`, `setup_centralizerQuotient`, `exists_fgh_centralizer_eq`,
  `fgh_map_centralizerQuotient` — the same for `C = C_G(X)` and `C/𝒩(C)`, whose standing
  data `PSU3SectionFourSetup` already supplies in full.
* `SectionFourSetup.isStandardModel_centralizerQuotient` — hence the Proposition of
  Ch. III §3 on `C/𝒩(C)`, with no residual hypothesis about the quotient.
* `map_Q0_of_mulEquiv`, `map_W_of_mulEquiv`, `exists_ne_one_mem_W_of_mulEquiv` — `Q₀` and
  `W` are determined by `H` and `D`, so any isomorphism matching those matches them, with
  no reference to `t`.  This is how step (2) moves `1 ≠ w ∈ W` between the intrinsic and
  the transported standing hypotheses on `U/Z(U)`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.RankOneBNPair
open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {X : Subgroup G}

/-! ### `U` read in `G` versus `U` read in `C_G(X)`

`residual X` is `O^{2′}(C_G(X))` as a subgroup of `C_G(X)`, which is where Ch. I §3
Proposition 1(c) identifies `U/Z(U)`; `residualImage X` is the same group as a subgroup of
`G`, which is where the rank-one setup lives (a `Setup` needs `H`, `Q`, `D` and `t` inside
one group).  The two are isomorphic because `C_G(X).subtype` is injective. -/

/-- **`U` computed in `C_G(X)` and in `G` agree.** -/
noncomputable def residualImageMulEquiv (X : Subgroup G) :
    ↥(residual (G := G) X) ≃* ↥(residualImage (G := G) X) :=
  Subgroup.equivMapOfInjective _ (Subgroup.centralizer (X : Set G)).subtype
    (Subgroup.subtype_injective _)

/-- **`U/Z(U)` computed in `C_G(X)` and in `G` agree.** -/
noncomputable def residualQuotientMulEquiv (X : Subgroup G) :
    (↥(residual (G := G) X) ⧸ Subgroup.center ↥(residual (G := G) X)) ≃*
      (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)) :=
  OddOrder.GroupTheory.quotientCenterCongr (residualImageMulEquiv (G := G) X)

/-! ### The two parities

`ofRankOneSetup` wants `|Q̄|` even and `|D̄|` odd for the *intrinsic* `Q̄ = π(U ∩ Q)` and
`D̄ = π(U ∩ D)`.  Both come from `U` itself, with no reference to the model: the quotient
map is injective on `U ∩ Q` (its kernel `Z(U)` lies in `D`, and `Q ∩ D = 1`), and `D̄` is a
quotient of a subgroup of `D`. -/

/-- **`U ∩ Q = C_Q(X)`** — one inclusion is `U ≤ C_G(X)`, the other is that a `2`-group
inside the centralizer lies in its `2′`-residual. -/
theorem Q_inf_residualImage_eq (hCQ : IsPGroup 2
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) :
    hyp.Q ⊓ residualImage (G := G) X = hyp.Q ⊓ Subgroup.centralizer (X : Set G) :=
  le_antisymm (inf_le_inf_left _ (Subgroup.map_subtype_le _))
    (le_inf inf_le_left (hyp.inf_centralizer_le_residual hCQ))

/-- The quotient map is injective on `U ∩ Q`: its kernel is `Z(U)`, which lies in `D` by
hypothesis, and `Q ∩ D = 1` in a rank-one setup. -/
theorem Q_subgroupOf_inf_center_eq_bot (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    hyp.Q.subgroupOf (residualImage (G := G) X)
      ⊓ Subgroup.center ↥(residualImage (G := G) X) = ⊥ :=
  le_bot_iff.mp ((inf_le_inf_left _ hZD).trans_eq
    (hyp.rankOneSetup_residual hXD htX hCQ).Q_inf_D_eq_bot)

/-- **`Q̄ ≃ C_Q(X)`** — `π` is injective on `U ∩ Q` and `U ∩ Q = C_Q(X)`, so the two
descriptions of the root group of `U/Z(U)` agree.  This is what carries the facts Ch. I §3
Proposition 1(c) proves about `C_Q(X)` — its order and its being a Suzuki `2`-group — over
to the intrinsic standing hypothesis. -/
noncomputable def cQMulEquivMapQ (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
      ≃* ↥((hyp.Q.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)))) :=
  ((OddOrder.GroupTheory.subgroupOfMulEquivInf hyp.Q
        (Subgroup.centralizer (X : Set G))).trans
      (MulEquiv.subgroupCongr (hyp.Q_inf_residualImage_eq hCQ).symm)).trans
    ((OddOrder.GroupTheory.subgroupOfMulEquivInf hyp.Q (residualImage (G := G) X)).symm.trans
      (OddOrder.GroupTheory.mapMk'MulEquiv (hyp.Q_subgroupOf_inf_center_eq_bot hXD htX hCQ hZD)))

/-- **`|Q̄| = |C_Q(X)|`**, which is the form §2 and §3 want (`|Q̄| = ℓ³`). -/
theorem natCard_map_Q_residualQuotient (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Nat.card ↥((hyp.Q.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      = Nat.card ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) :=
  (Nat.card_congr (hyp.cQMulEquivMapQ hXD htX hCQ hZD).toEquiv).symm

/-- **`|D̄|` is odd** — `D̄` is a quotient of `U ∩ D ≤ D`, and `|D|` is odd by (A2). -/
theorem odd_natCard_map_D_residualQuotient :
    Odd (Nat.card ↥((hyp.D.subgroupOf (residualImage (G := G) X)).map
      (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))) := by
  have hdvd₁ : Nat.card ↥((hyp.D.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      ∣ Nat.card ↥(hyp.D.subgroupOf (residualImage (G := G) X)) :=
    Subgroup.card_dvd_of_surjective _
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' _) _)
  have hdvd₂ : Nat.card ↥(hyp.D.subgroupOf (residualImage (G := G) X))
      ∣ Nat.card ↥hyp.D := by
    rw [OddOrder.GroupTheory.natCard_subgroupOf]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact Odd.of_dvd_nat hyp.D_odd (hdvd₁.trans hdvd₂)

/-- **Commuting with `C_Q(X)` modulo `Z(U)` is commuting on the nose**, for an element of
`U ∩ D` — the `U/Z(U)` counterpart of `commute_of_commute_mk'_of_mem_D_of_mem_Q`.

Same reason: the commutator lies in `U ∩ Q`, the kernel `Z(U)` lies in `U ∩ D`, and
`Q ∩ D = 1`.  It turns "`w̄` centralizes `Q̄₀`" — which is what `W̄ = D̄ ⊓ C(Q̄₀)` asks —
into a statement about `C_{Q₀}(X)` upstairs. -/
theorem commute_of_commute_mk'_center_of_mem_D_of_mem_Q (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X))
    {v u : ↥(residualImage (G := G) X)}
    (hv : v ∈ hyp.D.subgroupOf (residualImage (G := G) X))
    (hu : u ∈ hyp.Q.subgroupOf (residualImage (G := G) X))
    (h : QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)) v *
        QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)) u
      = QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)) u *
        QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)) v) :
    v * u = u * v := by
  classical
  have hcommZ : v * u * v⁻¹ * u⁻¹ ∈ Subgroup.center ↥(residualImage (G := G) X) := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    have hrw : (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)))
        (v * u * v⁻¹ * u⁻¹)
        = (QuotientGroup.mk' _ v * QuotientGroup.mk' _ u) *
          (QuotientGroup.mk' _ u * QuotientGroup.mk' _ v)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    have := hrw
    rw [h, mul_inv_cancel] at this
    simpa using this
  have hcommQ : v * u * v⁻¹ * u⁻¹ ∈ hyp.Q.subgroupOf (residualImage (G := G) X) := by
    refine (hyp.Q.subgroupOf (residualImage (G := G) X)).mul_mem ?_
      ((hyp.Q.subgroupOf (residualImage (G := G) X)).inv_mem hu)
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hvH : (v : G) ∈ hyp.H := hyp.D_le_H (Subgroup.mem_subgroupOf.mp hv)
    have := hyp.Q_normal_in_H (v : G) hvH (u : G) (Subgroup.mem_subgroupOf.mp hu)
    simpa using this
  have hbot : v * u * v⁻¹ * u⁻¹ ∈ hyp.Q.subgroupOf (residualImage (G := G) X)
      ⊓ hyp.D.subgroupOf (residualImage (G := G) X) := ⟨hcommQ, hZD hcommZ⟩
  rw [(hyp.rankOneSetup_residual hXD htX hCQ).Q_inf_D_eq_bot, Subgroup.mem_bot] at hbot
  have hvu : v * u * v⁻¹ = u := mul_inv_eq_one.mp hbot
  calc v * u = v * u * v⁻¹ * v := by group
    _ = u * v := by rw [hvu]

/-! ### The same transfers for `C = C_G(X)` and `C/𝒩(C)`

`PSU3SectionFourSetup.standingData_centralizerQuotient` supplies *every* input of Ch. I §3
Lemma 5 — including the `1 ≠ w ∈ W̄` the book gets from `|(V ∩ U)/(P ∩ U)| ≠ 1` — for the
standing hypothesis `centralizerQuotientHypothesis` on `C/𝒩(C)`, whose `H`, `Q`, `D` are
already the images of `C_H(X)`, `C_Q(X)`, `C_D(X)`.  Since `O^{2′}(C/𝒩(C)) ≅ U/Z(U)`, that
group is `PSU(3, ℓ)` extended by an odd-order group, and the transfers of step (2) work
there verbatim: `C` inherits the rank-one setup for the same reason `U` does, and
`𝒩(C) = C_D(X) ⊓ C_{C}(C_Q(X))` lies in `D`, so the setup descends to `C/𝒩(C)`. -/

/-- **`C = C_G(X)` inherits the rank-one setup** — the case `K = C` of
`rankOneSetup_subgroup`. -/
theorem rankOneSetup_centralizer (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G)) :
    Setup (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G)))
      (hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
      (hyp.D.subgroupOf (Subgroup.centralizer (X : Set G)))
      (⟨hyp.t, htX⟩ : ↥(Subgroup.centralizer (X : Set G))) :=
  hyp.rankOneSetup_subgroup hXD htX le_rfl htX inf_le_right

/-- **`C/𝒩(C)` inherits it too** — `𝒩(C) = C_D(X) ⊓ C_C(C_Q(X))` lies in `C_D(X)`
(`normalCore_cH_eq_centralizer_cQ`), which is a legitimate kernel for `Setup.quotient`.

The three images are exactly the `H`, `Q`, `D` of `centralizerQuotientHypothesis`, so the
mappings `Setup.exists_fgh` produces here are that hypothesis's `f`, `g`, `h`. -/
theorem setup_centralizerQuotient (hXV : X ≤ hyp.V) (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G)) :
    Setup
      ((hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).map
        (QuotientGroup.mk' (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore))
      ((hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))).map
        (QuotientGroup.mk' (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore))
      ((hyp.D.subgroupOf (Subgroup.centralizer (X : Set G))).map
        (QuotientGroup.mk' (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore))
      (QuotientGroup.mk' (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore
        ⟨hyp.t, htX⟩) :=
  (hyp.rankOneSetup_centralizer hXD htX).quotient
    (by rw [hyp.normalCore_cH_eq_centralizer_cQ hXV]; exact inf_le_left)

/-- **The mappings relative to `C`, `C ∩ H` and `t` exist in `G` and agree with the
ambient ones on `(Q ∩ C)^#`** — the `C`-version of `exists_fgh_residual_eq`. -/
theorem exists_fgh_centralizer_eq {f g h : G → G}
    (Hfgh : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h) (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G)) :
    ∃ f₁ g₁ h₁ : G → G,
      IsFGH (hyp.H ⊓ Subgroup.centralizer (X : Set G))
          (hyp.Q ⊓ Subgroup.centralizer (X : Set G))
          (hyp.D ⊓ Subgroup.centralizer (X : Set G)) hyp.t f₁ g₁ h₁ ∧
        ∀ x ∈ hyp.Q ⊓ Subgroup.centralizer (X : Set G), x ≠ 1 →
          f x = f₁ x ∧ g x = g₁ x ∧ h x = h₁ x := by
  obtain ⟨f₁, g₁, h₁, H₁⟩ := (hyp.rankOneSetup_centralizer hXD htX).exists_fgh
  refine ⟨liftMap _ f₁, liftMap _ g₁, liftMap _ h₁, H₁.ofSubtype, fun x hx hx1 => ?_⟩
  exact IsFGH.eq_of_le hyp.rankOneSetup Hfgh inf_le_left inf_le_left H₁.ofSubtype hx hx1

/-- **The mappings of `C/𝒩(C)` are the images of those of `C`** — the `C`-version of
`fgh_map_residualQuotient`, and the direction that reads §3's Corollary 2 back inside
`C_G(X)`. -/
theorem fgh_map_centralizerQuotient (hXV : X ≤ hyp.V) (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    {f₁ g₁ h₁ : ↥(Subgroup.centralizer (X : Set G)) → ↥(Subgroup.centralizer (X : Set G))}
    (H₁ : IsFGH (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G)))
      (hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
      (hyp.D.subgroupOf (Subgroup.centralizer (X : Set G)))
      ⟨hyp.t, htX⟩ f₁ g₁ h₁)
    {fb gb hb :
      (↥(Subgroup.centralizer (X : Set G)) ⧸
          (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore) →
        (↥(Subgroup.centralizer (X : Set G)) ⧸
          (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore)}
    (Hb : IsFGH
      ((hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).map
        (QuotientGroup.mk' (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore))
      ((hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))).map
        (QuotientGroup.mk' (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore))
      ((hyp.D.subgroupOf (Subgroup.centralizer (X : Set G))).map
        (QuotientGroup.mk' (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore))
      (QuotientGroup.mk' (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore
        ⟨hyp.t, htX⟩) fb gb hb)
    {x : ↥(Subgroup.centralizer (X : Set G))}
    (hxQ : x ∈ hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
    (hx1 : QuotientGroup.mk'
      (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore x ≠ 1) :
    fb (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (f₁ x) ∧
      gb (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (g₁ x) ∧
      hb (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (h₁ x) :=
  IsFGH.map (hyp.setup_centralizerQuotient hXV hXD htX) H₁ Hb
    (QuotientGroup.mk' _) rfl (fun _ hy => Subgroup.mem_map_of_mem _ hy)
    (fun _ hy => Subgroup.mem_map_of_mem _ hy) hxQ hx1

/-! ### `f₁`, `h₁` relative to `U`, and their agreement with `f`, `h`

Step (2) ends by reading the conclusion it gets on `U` back inside `G`: "By the uniqueness
of the canonical form of an element of `G − H`, `f(ω) = f₁(ω)` … and `h(ω) = h₁(ω)`"
(p. 133).  Formally: the setup `U` inherits produces mappings `↥U → ↥U`, which read in `G`
(`liftMap`) factor `t x t` with factors in `Q ∩ U ≤ Q` and `D ∩ U ≤ D`; `IsFGH.eq_of_le`
is exactly the uniqueness the book invokes. -/

/-- **The mappings relative to `U`, `U ∩ H` and `t` exist in `G` and agree with the
ambient ones on `(Q ∩ U)^#`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133). -/
theorem exists_fgh_residual_eq {f g h : G → G}
    (Hfgh : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h) (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) :
    ∃ f₁ g₁ h₁ : G → G,
      IsFGH (hyp.H ⊓ residualImage (G := G) X) (hyp.Q ⊓ residualImage (G := G) X)
          (hyp.D ⊓ residualImage (G := G) X) hyp.t f₁ g₁ h₁ ∧
        ∀ x ∈ hyp.Q ⊓ residualImage (G := G) X, x ≠ 1 →
          f x = f₁ x ∧ g x = g₁ x ∧ h x = h₁ x := by
  obtain ⟨f₁, g₁, h₁, H₁⟩ := (hyp.rankOneSetup_residual hXD htX hCQ).exists_fgh
  refine ⟨liftMap _ f₁, liftMap _ g₁, liftMap _ h₁, H₁.ofSubtype, fun x hx hx1 => ?_⟩
  exact IsFGH.eq_of_le hyp.rankOneSetup Hfgh inf_le_left inf_le_left H₁.ofSubtype hx hx1

/-- **The mappings of `U/Z(U)` are the images of those of `U`** (Peterfalvi Part II,
Ch. IV §4, step (2), p. 133).

This is the other half of step (2)'s transfer: `Corollary 2` of §3 is proved on
`U/Z(U)`, and its conclusions are read back inside `U` "modulo the kernel", which is the
book's `P ∩ U = Z(U)`. -/
theorem fgh_map_residualQuotient (hXD : X ≤ hyp.D)
    (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X))
    {f₁ g₁ h₁ : ↥(residualImage (G := G) X) → ↥(residualImage (G := G) X)}
    (H₁ : IsFGH (hyp.H.subgroupOf (residualImage (G := G) X))
      (hyp.Q.subgroupOf (residualImage (G := G) X))
      (hyp.D.subgroupOf (residualImage (G := G) X))
      ⟨hyp.t, hyp.t_mem_residual htX⟩ f₁ g₁ h₁)
    {fb gb hb : (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X))
      → (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X))}
    (Hb : IsFGH
      ((hyp.H.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      ((hyp.Q.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      ((hyp.D.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))
        ⟨hyp.t, hyp.t_mem_residual htX⟩) fb gb hb)
    {x : ↥(residualImage (G := G) X)}
    (hxQ : x ∈ hyp.Q.subgroupOf (residualImage (G := G) X))
    (hx1 : QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)) x ≠ 1) :
    fb (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (f₁ x) ∧
      gb (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (g₁ x) ∧
      hb (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (h₁ x) :=
  IsFGH.map (hyp.setup_residualQuotient hXD htX hCQ hZD) H₁ Hb
    (QuotientGroup.mk' _) rfl (fun _ hy => Subgroup.mem_map_of_mem _ hy)
    (fun _ hy => Subgroup.mem_map_of_mem _ hy) hxQ hx1

/-- `|U/Z(U)| < |G|`, read in `G` — the bound the induction hypothesis restricts along. -/
theorem natCard_residualImageQuotient_lt (hXV : X ≤ hyp.V) (hX : X ≠ ⊥) :
    Nat.card (↥(residualImage (G := G) X) ⧸
      Subgroup.center ↥(residualImage (G := G) X)) < Nat.card G := by
  rw [← Nat.card_congr (residualQuotientMulEquiv (G := G) X).toEquiv]
  exact hyp.natCard_residualQuotient_lt hXV hX

/-- The distinguished involution lies in `U`: it centralizes `X` (Ch. I §3) and is an
involution, so it lies in the `2′`-residual. -/
theorem distinguishedInvolution_mem_residualImage (hXV : X ≤ hyp.V) :
    hyp.distinguishedInvolution ∈ residualImage (G := G) X :=
  sq_eq_one_mem_residual hyp.distinguishedInvolution_sq
    (hyp.distinguishedInvolution_mem_centralizer_of_le_V hXV)

/-- The structure conjugator lies in `U`: it centralizes `X` (Ch. I §3) and lies in `Q`,
and `C_Q(X) ≤ U`. -/
theorem structureConjugator_mem_residualImage (hXV : X ≤ hyp.V)
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))) :
    hyp.structureConjugator ∈ residualImage (G := G) X :=
  hyp.inf_centralizer_le_residual hCQ (Subgroup.mem_inf.mpr
    ⟨hyp.structureConjugator_mem_Q, hyp.structureConjugator_mem_centralizer_of_le_V hXV⟩)

/-! ### Commuting with `Q̄` is commuting with `C_Q(X)`

`hVW` for `C/𝒩(C)` reduces, by `V_eq_W_iff_le_centralizer_Q0`, to `V̄ ≤ C(Q̄₀)`, i.e. to a
commuting relation *modulo* `𝒩(C)`.  The kernel drops out on the `Q`-side: a commutator of
`C_D(X)` with `C_Q(X)` lies in `C_Q(X)`, while `𝒩(C) = C_D(X) ⊓ C_C(C_Q(X))` lies in
`C_D(X)`, and `C_Q(X) ∩ C_D(X) = 1`. -/

/-- **Commuting with `C_Q(X)` modulo `𝒩(C)` is commuting on the nose**, for an element of
`C_D(X)`. -/
theorem commute_of_commute_mk'_of_mem_D_of_mem_Q (hXV : X ≤ hyp.V)
    {v u : ↥(Subgroup.centralizer (X : Set G))}
    (hv : v ∈ hyp.D.subgroupOf (Subgroup.centralizer (X : Set G)))
    (hu : u ∈ hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)))
    (h : QuotientGroup.mk'
          (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore v *
        QuotientGroup.mk'
          (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore u
      = QuotientGroup.mk'
          (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore u *
        QuotientGroup.mk'
          (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore v) :
    v * u = u * v := by
  classical
  have hcommN : v * u * v⁻¹ * u⁻¹ ∈
      (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    have hmk : (QuotientGroup.mk'
        (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore)
        (v * u * v⁻¹ * u⁻¹) = 1 := by
      have hrw : (QuotientGroup.mk'
          (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore)
            (v * u * v⁻¹ * u⁻¹)
          = (QuotientGroup.mk' _ v * QuotientGroup.mk' _ u) *
            (QuotientGroup.mk' _ u * QuotientGroup.mk' _ v)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      rw [hrw, h, mul_inv_cancel]
    simpa using hmk
  have hvH : v ∈ hyp.H.subgroupOf (Subgroup.centralizer (X : Set G)) :=
    Subgroup.mem_subgroupOf.mpr (hyp.D_le_H (Subgroup.mem_subgroupOf.mp hv))
  have hcommQ : v * u * v⁻¹ * u⁻¹ ∈
      hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G)) :=
    (hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))).mul_mem
      ((hyp.centralizerHypothesisA1 hXV).Q_normal_in_H v hvH u hu)
      ((hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))).inv_mem hu)
  have hNleD : (hyp.H.subgroupOf (Subgroup.centralizer (X : Set G))).normalCore
      ≤ hyp.D.subgroupOf (Subgroup.centralizer (X : Set G)) := by
    rw [hyp.normalCore_cH_eq_centralizer_cQ hXV]
    exact inf_le_left
  have hbot : v * u * v⁻¹ * u⁻¹ ∈
      hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))
        ⊓ hyp.D.subgroupOf (Subgroup.centralizer (X : Set G)) :=
    ⟨hcommQ, hNleD hcommN⟩
  have hQD : hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))
      ⊓ hyp.D.subgroupOf (Subgroup.centralizer (X : Set G)) = ⊥ :=
    (hyp.centralizerHypothesisA1 hXV).Q_inf_D_eq_bot
  rw [hQD, Subgroup.mem_bot] at hbot
  have hvu : v * u * v⁻¹ = u := mul_inv_eq_one.mp hbot
  calc v * u = v * u * v⁻¹ * v := by group
    _ = u * v := by rw [hvu]

/-! ### `Z(Q̄) = Q̄₀` for the centralizer quotient

`corollaryTwo_of_standardModel` takes `hZc : Z(Q) = Q₀ ∩ Q`, which for `C/𝒩(C)` reduces to
"`Z(Q̄)` has exponent `2`" (`center_Q_eq_Q0_subgroupOf_of_sq_eq_one`).  That is a fact
about the root group: `Q̄ ≅ C_Q(X)` (`centralizerQQuotientEquiv`), Ch. I §3 Proposition 1(c)
identifies `C_Q(X)` with `RootGroup ℓ` (`cQEquivRoot`), and `Z(RootGroup ℓ)` is the
square-one central line (`RootGroup.center_eq_centerLine`).

The identification is taken as a parameter rather than read off `CentralizerPSUData`, so
that the statement does not depend on which `MulAction` instance the caller has in
scope. -/

/-- Every central element of `Q̄` is an involution, because `Z(RootGroup ℓ)` is the
square-one central line. -/
theorem sq_eq_one_of_mem_center_Q_centralizerQuotient (hXV : X ≤ hyp.V) {n : ℕ} (hn : 0 < n)
    (eRoot : ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) ≃* RootGroup n)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    letI := hyp.centralizerQuotientMulAction hXV
    ∀ z ∈ Subgroup.center ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q, z ^ 2 = 1 := by
  letI := hyp.centralizerQuotientMulAction hXV
  intro z hz
  set e : ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q ≃* RootGroup n :=
    (hyp.centralizerQQuotientEquiv hXV).symm.trans eRoot with he
  have hcz : e z ∈ Subgroup.center (RootGroup n) :=
    (MulEquivClass.apply_mem_center_iff e).mpr hz
  rw [RootGroup.center_eq_centerLine n hn, RootGroup.mem_centerLine_iff_sq_eq_one] at hcz
  exact e.injective (by rw [map_pow, hcz, map_one])

/-- **`Z(Q̄) = Q̄₀ ∩ Q̄`** — `corollaryTwo_of_standardModel`'s `hZc` for `C/𝒩(C)`. -/
theorem center_Q_eq_Q0_centralizerQuotient (hXV : X ≤ hyp.V) {n : ℕ} (hn : 0 < n)
    (eRoot : ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))) ≃* RootGroup n)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer (X : Set G)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    letI := hyp.centralizerQuotientMulAction hXV
    Subgroup.center ↥(hyp.centralizerQuotientHypothesis hXV hA3).Q
      = (hyp.centralizerQuotientHypothesis hXV hA3).Q0.subgroupOf
        (hyp.centralizerQuotientHypothesis hXV hA3).Q := by
  letI := hyp.centralizerQuotientMulAction hXV
  exact (hyp.centralizerQuotientHypothesis hXV hA3).center_Q_eq_Q0_subgroupOf_of_sq_eq_one
    (hyp.sq_eq_one_of_mem_center_Q_centralizerQuotient hXV hn eRoot hA3)


section Model

variable [MulAction (hyp.centralizerActionQuotient X) ↥(MulAction.fixedPoints X Ω)]
  {result : TheoremAConclusion (hyp.centralizerActionQuotient X)
    ↥(MulAction.fixedPoints X Ω)}
  {data : PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Ω)) result.L}

/-- **`U/Z(U) ≃ PSU(3, ℓ)`, read in `G`** — Ch. I §3 Proposition 1(c) states the
identification for the residual inside `C_G(X)`; this moves it to the residual's image in
`G`, where the rank-one setup of step (2) lives. -/
noncomputable def residualQuotientImageEquiv (details : CentralizerPSUData hyp X result data) :
    (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)) ≃*
      standardPermGroup data.n :=
  (residualQuotientMulEquiv (G := G) X).symm.trans details.residualQuotientEquiv

/-- **`U/Z(U)` is simple** (Peterfalvi Part II, Ch. I §3, Lemma 1, via Proposition 1(c)).

This is the faithfulness input of `Hypothesis.ofRankOneSetup`: a proper subgroup of a
simple group has trivial normal core, and `M̄ = π(U ∩ H)` is proper because `t̄ ∉ M̄`. -/
theorem isSimpleGroup_residualQuotient (details : CentralizerPSUData hyp X result data) :
    IsSimpleGroup (↥(residualImage (G := G) X) ⧸
      Subgroup.center ↥(residualImage (G := G) X)) :=
  letI := standardPermGroup_isSimpleGroup data.one_lt_n
  (hyp.residualQuotientImageEquiv details).isSimpleGroup

/-- **(A3) holds on `U/Z(U)`** — the standard model has `2`-rank at least two and that is
a property of the group alone, so any identification transports it. -/
theorem two_rank_ge_two_residualQuotient (details : CentralizerPSUData hyp X result data) :
    ∃ E : Subgroup (↥(residualImage (G := G) X) ⧸
        Subgroup.center ↥(residualImage (G := G) X)),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  obtain ⟨E, hcard, hsq⟩ := (standardHypothesis data.n data.one_lt_n).two_rank_ge_two
  set e := (hyp.residualQuotientImageEquiv details).symm
  refine ⟨E.map (e : _ →* _), ?_, ?_⟩
  · rw [← hcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective E _ e.injective).toEquiv).symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hsq x hx, map_one]

/-- **`|Q̄|` is even** — it equals `|C_Q(X)| = ℓ³` by `natCard_map_Q_residualQuotient`, and
`ℓ = 2ⁿ` with `n ≥ 2`. -/
theorem even_natCard_map_Q_residualQuotient (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Even (Nat.card ↥((hyp.Q.subgroupOf (residualImage (G := G) X)).map
      (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))) := by
  have hn := data.one_lt_n
  rw [hyp.natCard_map_Q_residualQuotient hXD htX hCQ hZD,
    details.natCard_cQ_eq_baseField_cube, natCard_baseField data.n (by omega)]
  obtain ⟨k, hk⟩ :=
    (dvd_pow_self (2 : ℕ) (by omega : data.n ≠ 0)).trans
      (dvd_pow_self ((2 : ℕ) ^ data.n) (by norm_num : (3 : ℕ) ≠ 0))
  exact ⟨k, by omega⟩

/-- **The standing hypothesis on `U/Z(U)`, in the intrinsic subgroups** (Peterfalvi
Part II, Ch. IV §4, step (2), p. 133).

This is what step (2) argues with: `H`, `Q`, `D` and `t` are the images of `U ∩ H`,
`U ∩ Q`, `U ∩ D` and `t`, so the mappings `Setup.exists_fgh` produces for it are the
book's `f₁` and `h₁` "relative to `U`, `U ∩ H` and `t`", and §2 and §3 applied to it are
§2 and §3 "relative to `U`".

`residualQuotientHypothesis` also puts a standing hypothesis on this group, but by
transporting the standard model's, so its `H`, `Q`, `D` are whatever the identification
produces; the two agree on everything that only depends on the group (`|Q̄|` and the
simplicity used here), which is why the numerical inputs of §2 and §3 can be quoted from
either. -/
noncomputable def intrinsicResidualQuotient (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Hypothesis (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X))
      ((↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)) ⧸
        (hyp.H.subgroupOf (residualImage (G := G) X)).map
          (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)))) :=
  letI := hyp.isSimpleGroup_residualQuotient details
  Hypothesis.ofRankOneSetup (hyp.setup_residualQuotient hXD htX hCQ hZD)
    (hyp.setup_residualQuotient hXD htX hCQ hZD).normalCore_eq_bot_of_isSimpleGroup
    (hyp.even_natCard_map_Q_residualQuotient details hXD htX hCQ hZD)
    hyp.odd_natCard_map_D_residualQuotient
    (hyp.two_rank_ge_two_residualQuotient details)

/-! ### The numerical inputs of §2 and §3, intrinsically

`exists_standardModel` takes `|Q̄₀| = ℓ` and `|Q̄| = |Q̄₀|³`.  For the intrinsic hypothesis
those are statements about `π(U ∩ Q₀)` and `π(U ∩ Q)`, and both reduce to `C_{Q₀}(X)` and
`C_Q(X)` for the same reason: `Z(U)` lies in `D`, which meets `Q ⊇ Q₀` trivially. -/

@[simp] theorem intrinsicResidualQuotient_H (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).H
      = (hyp.H.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))) := rfl

@[simp] theorem intrinsicResidualQuotient_Q (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q
      = (hyp.Q.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))) := rfl

/-- **`|Z(U)|` is odd, read in `G`** — Ch. I §3 Proposition 1(c) proves it for the residual
inside `C_G(X)` (`odd_natCard_center_residual`), and the two centres correspond. -/
theorem odd_natCard_center_residualImage (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data) :
    Odd (Nat.card ↥(Subgroup.center ↥(residualImage (G := G) X))) := by
  have hcard : Nat.card ↥(Subgroup.center ↥(residualImage (G := G) X))
      = Nat.card ↥(Subgroup.center ↥(residual (G := G) X)) := by
    rw [← OddOrder.GroupTheory.map_center_mulEquiv (residualImageMulEquiv (G := G) X)]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (residualImageMulEquiv (G := G) X).injective).toEquiv).symm
  have hnd := details.odd_natCard_center_residual hXV common
  rw [hcard]
  rcases Nat.even_or_odd (Nat.card ↥(Subgroup.center ↥(residual (G := G) X))) with he | ho
  · obtain ⟨r, hr⟩ := he
    have h2 : (2 : ℕ) ∣ Nat.card ↥(Subgroup.center ↥(residual (G := G) X)) := ⟨r, by omega⟩
    exact absurd h2 hnd
  · exact ho

/-- **`Q̄₀ = π(U ∩ Q₀)`** — the involutions of `M̄` are exactly the images of the
involutions of `U ∩ H`.

One direction is trivial.  For the other, `x̄² = 1` only says `x² ∈ Z(U)`; the lift is
`x^{|Z(U)|}`, which squares to `1` and has the same image because `|Z(U)|` is odd
(`sq_pow_natCard_eq_one_of_sq_mem`). -/
theorem Q0_intrinsicResidualQuotient_eq (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q0
      = (hyp.Q0.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))) := by
  classical
  have hodd := hyp.odd_natCard_center_residualImage hXV common details
  ext y
  rw [Hypothesis.mem_Q0_iff, hyp.intrinsicResidualQuotient_H details hXD htX hCQ hZD]
  constructor
  · rintro ⟨hy2, x, hxH, rfl⟩
    have hxsq : x ^ 2 ∈ Subgroup.center ↥(residualImage (G := G) X) := by
      refine (QuotientGroup.eq_one_iff (x ^ 2)).mp ?_
      rw [← QuotientGroup.mk'_apply, map_pow]
      exact hy2
    obtain ⟨hsq, hdiff⟩ := OddOrder.GroupTheory.sq_pow_natCard_eq_one_of_sq_mem hodd hxsq
    refine ⟨x ^ Nat.card ↥(Subgroup.center ↥(residualImage (G := G) X)), ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
      · have := congrArg (Subtype.val (p := fun z => z ∈ residualImage (G := G) X)) hsq
        push_cast at this
        exact this
      · exact hyp.H.pow_mem (Subgroup.mem_subgroupOf.mp hxH) _
    · exact (QuotientGroup.eq.mpr hdiff).symm
  · rintro ⟨x, hxQ0, rfl⟩
    have hxG : (x : G) ∈ hyp.Q0 := Subgroup.mem_subgroupOf.mp hxQ0
    have hxsq : (x : ↥(residualImage (G := G) X)) ^ 2 = 1 :=
      Subtype.ext (by push_cast; exact hxG.1)
    refine ⟨?_, ⟨(x : ↥(residualImage (G := G) X)),
      Subgroup.mem_subgroupOf.mpr hxG.2, rfl⟩⟩
    rw [← map_pow, hxsq, map_one]

/-- **`|Q̄₀| = ℓ`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133) — one of the two
numerical inputs of the Proposition of Ch. III §3, in the intrinsic subgroups. -/
theorem natCard_Q0_intrinsicResidualQuotient (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Nat.card ↥(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q0 = 2 ^ data.n := by
  have hn := data.one_lt_n
  have hmono : hyp.Q0.subgroupOf (residualImage (G := G) X)
      ≤ hyp.Q.subgroupOf (residualImage (G := G) X) := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (hyp.Q0_le_Q (Subgroup.mem_subgroupOf.mp hz))
  have hbot : hyp.Q0.subgroupOf (residualImage (G := G) X)
      ⊓ Subgroup.center ↥(residualImage (G := G) X) = ⊥ :=
    le_bot_iff.mp (((inf_le_inf hmono hZD).trans_eq
      (hyp.rankOneSetup_residual hXD htX hCQ).Q_inf_D_eq_bot))
  have hinf : hyp.Q0 ⊓ residualImage (G := G) X
      = hyp.Q0 ⊓ Subgroup.centralizer (X : Set G) :=
    le_antisymm (inf_le_inf_left _ (Subgroup.map_subtype_le _))
      (le_inf inf_le_left ((inf_le_inf_right _ hyp.Q0_le_Q).trans
        (hyp.inf_centralizer_le_residual hCQ)))
  rw [hyp.Q0_intrinsicResidualQuotient_eq hXV common details hXD htX hCQ hZD,
    OddOrder.GroupTheory.natCard_map_mk'_of_inf_eq_bot hbot,
    OddOrder.GroupTheory.natCard_subgroupOf, hinf,
    ← OddOrder.GroupTheory.natCard_subgroupOf, details.natCard_cQ0_eq_baseField,
    natCard_baseField data.n (by omega)]

/-- **`|Q̄| = |Q̄₀|³`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133) — the other
numerical input of the Proposition of Ch. III §3, in the intrinsic subgroups. -/
theorem natCard_Q_intrinsicResidualQuotient (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Nat.card ↥(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q
      = Nat.card ↥(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q0 ^ 3 := by
  have hn := data.one_lt_n
  rw [hyp.natCard_Q0_intrinsicResidualQuotient hXV common details hXD htX hCQ hZD,
    hyp.intrinsicResidualQuotient_Q details hXD htX hCQ hZD,
    hyp.natCard_map_Q_residualQuotient hXD htX hCQ hZD,
    details.natCard_cQ_eq_baseField_cube, natCard_baseField data.n (by omega)]

/-- **`Q̄` is a Suzuki `2`-group** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133) — the
third input of Ch. I §3 Lemma 5, in the intrinsic subgroups.

Ch. I §3 Proposition 1(c) proves it for `C_Q(X)` (`cQ_isSuzuki2Group`), and being a
Suzuki `2`-group is an isomorphism invariant (`IsSuzuki2Group.of_equiv`). -/
theorem isSuzuki2Group_Q_intrinsicResidualQuotient
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group
      ↥(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q := by
  rw [hyp.intrinsicResidualQuotient_Q details hXD htX hCQ hZD]
  exact OddOrder.GroupTheory.SpecificGroups.Suzuki.IsSuzuki2Group.of_equiv
    details.cQ_isSuzuki2Group (hyp.cQMulEquivMapQ hXD htX hCQ hZD)

/-! ### The distinguished involution of `U/Z(U)`

`exists_standardModel` takes `|s̄ t̄| = 3`.  The distinguished pair is a `Classical.choose`,
so it has to be *identified*: `s` and its structure conjugator `r` both centralize `X` when
`X ≤ V` (Ch. I §3), hence both lie in `U`, and their images satisfy the defining conditions
downstairs.  Uniqueness then gives `s̄ = π(s)`, and `|s̄ t̄| = 3` follows from `|s t| = 3`
because the only alternative, `s̄ t̄ = 1`, would put `t̄ = s̄` inside `M̄`. -/

/-- **`s̄ = π(s)`**: the distinguished involution of the intrinsic hypothesis on `U/Z(U)`
is the image of the ambient one. -/
theorem distinguishedInvolution_intrinsicResidualQuotient (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).distinguishedInvolution
      = QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))
        ⟨hyp.distinguishedInvolution, hyp.distinguishedInvolution_mem_residualImage hXV⟩ := by
  classical
  set Z : Subgroup ↥(residualImage (G := G) X) :=
    Subgroup.center ↥(residualImage (G := G) X) with hZ
  set sU : ↥(residualImage (G := G) X) :=
    ⟨hyp.distinguishedInvolution, hyp.distinguishedInvolution_mem_residualImage hXV⟩ with hsU
  set rU : ↥(residualImage (G := G) X) :=
    ⟨hyp.structureConjugator, hyp.structureConjugator_mem_residualImage hXV hCQ⟩ with hrU
  set tU : ↥(residualImage (G := G) X) := ⟨hyp.t, hyp.t_mem_residual htX⟩ with htU
  have hsqU : sU ^ 2 = 1 := Subtype.ext hyp.distinguishedInvolution_sq
  have hsH : QuotientGroup.mk' Z sU ∈
      (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).H :=
    ⟨sU, Subgroup.mem_subgroupOf.mpr hyp.distinguishedInvolution_mem_H, rfl⟩
  have hs2 : (QuotientGroup.mk' Z sU) ^ 2 = 1 := by rw [← map_pow, hsqU, map_one]
  have hs1 : QuotientGroup.mk' Z sU ≠ 1 := by
    intro hcon
    have h1 : sU = 1 :=
      OddOrder.GroupTheory.eq_one_of_sq_eq_one_of_odd_card
        (hyp.odd_natCard_center_residualImage hXV common details)
        ((QuotientGroup.eq_one_iff sU).mp hcon) hsqU
    exact hyp.distinguishedInvolution_ne_one (congrArg Subtype.val h1)
  have hrQ : QuotientGroup.mk' Z rU ∈
      (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q :=
    ⟨rU, Subgroup.mem_subgroupOf.mpr hyp.structureConjugator_mem_Q, rfl⟩
  have hstructU : tU * sU * tU = rU⁻¹ * tU * rU := Subtype.ext hyp.structure_equation
  have heq := congrArg (QuotientGroup.mk' Z) hstructU
  rw [map_mul, map_mul, map_mul, map_mul, map_inv] at heq
  exact ((hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).eq_distinguishedPair_of_structure
    hsH hs2 hs1 hrQ heq).1.symm

/-- **`|s̄ t̄| = 3` on `U/Z(U)`, intrinsically** (Peterfalvi Part II, Ch. IV §4, step (2),
p. 133).

`|s t| = 3` upstairs (`distinguishedProduct_order`) gives `|s̄ t̄| ∣ 3`, and `s̄ t̄ = 1` is
barred because it would put `t̄ = s̄` inside `M̄`. -/
theorem orderOf_distinguishedInvolution_mul_t_intrinsicResidualQuotient (hXV : X ≤ hyp.V)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    orderOf
        ((hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).distinguishedInvolution *
          (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).t) = 3 := by
  classical
  set hq := hyp.intrinsicResidualQuotient details hXD htX hCQ hZD with hqdef
  set Z : Subgroup ↥(residualImage (G := G) X) :=
    Subgroup.center ↥(residualImage (G := G) X) with hZ
  set sU : ↥(residualImage (G := G) X) :=
    ⟨hyp.distinguishedInvolution, hyp.distinguishedInvolution_mem_residualImage hXV⟩ with hsU
  set tU : ↥(residualImage (G := G) X) := ⟨hyp.t, hyp.t_mem_residual htX⟩ with htU
  have hcube : (sU * tU) ^ 3 = 1 := by
    refine Subtype.ext ?_
    change (hyp.distinguishedInvolution * hyp.t) ^ 3 = 1
    rw [← details.distinguishedProduct_order]
    exact pow_orderOf_eq_one _
  have hprod : hq.distinguishedInvolution * hq.t = QuotientGroup.mk' Z (sU * tU) := by
    rw [hqdef, hyp.distinguishedInvolution_intrinsicResidualQuotient hXV common details
      hXD htX hCQ hZD, map_mul]
    rfl
  have hdvd : orderOf (hq.distinguishedInvolution * hq.t) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [hprod, ← map_pow, hcube, map_one])
  have hne : hq.distinguishedInvolution * hq.t ≠ 1 := by
    intro hcon
    have hst : hq.distinguishedInvolution = hq.t⁻¹ := mul_eq_one_iff_eq_inv.mp hcon
    exact hq.t_not_mem_H
      (by rw [← hq.t_inv_eq, ← hst]; exact hq.distinguishedInvolution_mem_H)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h3

/-- **`Z(Q̄) = Q̄₀ ∩ Q̄` for the intrinsic hypothesis on `U/Z(U)`** —
`corollaryTwo_of_standardModel`'s `hZc`.

Same argument as `center_Q_eq_Q0_centralizerQuotient`: `Z(Q̄)` has exponent `2` because
`Q̄ ≅ C_Q(X) ≅ RootGroup ℓ` (`cQMulEquivMapQ`, `cQEquivRoot`) and `Z(RootGroup ℓ)` is the
square-one central line. -/
theorem center_Q_eq_Q0_intrinsicResidualQuotient
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    Subgroup.center ↥(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q
      = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q0.subgroupOf
        (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q := by
  refine (hyp.intrinsicResidualQuotient details hXD htX hCQ
    hZD).center_Q_eq_Q0_subgroupOf_of_sq_eq_one (fun z hz => ?_)
  have hn := data.one_lt_n
  set e : ↥(hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q ≃* RootGroup data.n :=
    (MulEquiv.subgroupCongr
        (hyp.intrinsicResidualQuotient_Q details hXD htX hCQ hZD)).trans
      ((hyp.cQMulEquivMapQ hXD htX hCQ hZD).symm.trans details.cQEquivRoot) with he
  have hcz : e z ∈ Subgroup.center (RootGroup data.n) :=
    (MulEquivClass.apply_mem_center_iff e).mpr hz
  rw [RootGroup.center_eq_centerLine data.n (by omega), RootGroup.mem_centerLine_iff_sq_eq_one]
    at hcz
  exact e.injective (by rw [map_pow, hcz, map_one])

/-! ### Matching the intrinsic and the transported standing hypotheses

`Setup.exists_conj_eq_triple` matches `Q`, `M` and `D` of any two rank-one setups on the
same group, and `Setup.map` moves the transported one from `U/Z(U)` computed in `C_G(X)`
to `U/Z(U)` computed in `G`.  Composing the two gives an isomorphism matching `H`, `Q`
and `D` — enough for `Q₀` and `W` (`map_W_of_mulEquiv`), which is what Ch. I §3 Lemma 5's
last input needs. -/

/-- A subgroup with more than one element is not trivial. -/
private theorem ne_bot_of_one_lt_natCard {A : Type*} [Group A] {K : Subgroup A}
    (h : 1 < Nat.card ↥K) : K ≠ ⊥ := by
  intro hc
  rw [hc, Subgroup.card_bot] at h
  exact absurd h (lt_irrefl 1)

/-- **The two standing hypotheses on `U/Z(U)` are matched on `H`, `Q`, `D`.** -/
theorem exists_mulEquiv_match_residualQuotient
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    ∃ φ : (↥(residual (G := G) X) ⧸ Subgroup.center ↥(residual (G := G) X)) ≃*
        (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)),
      (hyp.residualQuotientHypothesis details).H.map φ.toMonoidHom
          = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).H ∧
        (hyp.residualQuotientHypothesis details).Q.map φ.toMonoidHom
          = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q ∧
        (hyp.residualQuotientHypothesis details).D.map φ.toMonoidHom
          = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).D := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  classical
  have hn := data.one_lt_n
  set htr := hyp.residualQuotientHypothesis details with htrdef
  set e := residualQuotientMulEquiv (G := G) X with hedef
  have hcardmap : ∀ K : Subgroup (↥(residual (G := G) X) ⧸
      Subgroup.center ↥(residual (G := G) X)),
      Nat.card ↥(K.map e.toMonoidHom) = Nat.card ↥K := fun K =>
    (Nat.card_congr (Subgroup.equivMapOfInjective K e.toMonoidHom e.injective).toEquiv).symm
  -- the transported setup, moved to the `residualImage` side
  have hStr := htr.rankOneSetup.map e
  have hSint := hyp.setup_residualQuotient hXD htX hCQ hZD
  -- the eight numerical inputs
  have hQtr : IsPGroup 2 ↥(htr.Q.map e.toMonoidHom) :=
    (hyp.isSuzuki2Group_residualQuotientHypothesis_Q details).1.of_equiv
      (Subgroup.equivMapOfInjective htr.Q e.toMonoidHom e.injective)
  have hQcardtr : Nat.card ↥(htr.Q.map e.toMonoidHom) = (2 ^ data.n) ^ 3 := by
    rw [hcardmap, hyp.natCard_residualQuotientHypothesis_Q details,
      hyp.natCard_residualQuotientHypothesis_Q0 details]
  have hQevtr : Even (Nat.card ↥(htr.Q.map e.toMonoidHom)) := by
    rw [hcardmap]; exact htr.Q_even
  have hDoddtr : Odd (Nat.card ↥(htr.D.map e.toMonoidHom)) := by
    rw [hcardmap]; exact htr.D_odd
  have hcube : ∀ k : ℕ, 0 < k → 1 < (2 ^ k) ^ 3 := by
    intro k hk
    calc 1 < 2 := by norm_num
      _ = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
      _ ≤ (2 ^ k) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hQ1tr : htr.Q.map e.toMonoidHom ≠ ⊥ :=
    ne_bot_of_one_lt_natCard (by rw [hQcardtr]; exact hcube data.n (by omega))
  have hQint : IsPGroup 2 ↥((hyp.Q.subgroupOf (residualImage (G := G) X)).map
      (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)))) := by
    have h := hyp.isSuzuki2Group_Q_intrinsicResidualQuotient details hXD htX hCQ hZD
    rw [hyp.intrinsicResidualQuotient_Q details hXD htX hCQ hZD] at h
    exact h.1
  have hQcardint := hyp.natCard_map_Q_residualQuotient hXD htX hCQ hZD
  have hQ1int : (hyp.Q.subgroupOf (residualImage (G := G) X)).map
      (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))) ≠ ⊥ :=
    ne_bot_of_one_lt_natCard (by
      rw [hQcardint, details.natCard_cQ_eq_baseField_cube, natCard_baseField data.n (by omega)]
      exact hcube data.n (by omega))
  obtain ⟨c, hQc, hMc, hDc⟩ := hStr.exists_conj_eq_triple hSint hQtr hDoddtr hQevtr
    hQint (hyp.odd_natCard_map_D_residualQuotient)
    (hyp.even_natCard_map_Q_residualQuotient details hXD htX hCQ hZD) hQ1tr hQ1int
  have hcomp : (e.trans (MulAut.conj c)).toMonoidHom
      = (MulAut.conj c).toMonoidHom.comp e.toMonoidHom := by ext x; rfl
  refine ⟨e.trans (MulAut.conj c), ?_, ?_, ?_⟩
  · rw [hcomp, ← Subgroup.map_map]; exact hMc
  · rw [hcomp, ← Subgroup.map_map]; exact hQc
  · rw [hcomp, ← Subgroup.map_map]; exact hDc

/-- **🎯 `1 ≠ w ∈ W̄` for the intrinsic standing hypothesis on `U/Z(U)`** — the last input
of Ch. I §3 Lemma 5 (Peterfalvi Part II, Ch. IV §4, step (2), p. 133).

The book gets it from `|(V ∩ U)/(P ∩ U)| = (ℓ+1)/(ℓ+1,3) ≠ 1`; here it comes from the
transported hypothesis, where `exists_ne_one_mem_residualQuotientHypothesis_W` already has
it, along the isomorphism of `exists_mulEquiv_match_residualQuotient`.  `W = D ⊓ C(Q₀)`
depends only on `H` and `D`, so no matching of the distinguished involution is needed. -/
theorem exists_ne_one_mem_W_intrinsicResidualQuotient
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    ∃ w ∈ (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).W, w ≠ 1 := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  obtain ⟨φ, hH, _hQ, hD⟩ :=
    hyp.exists_mulEquiv_match_residualQuotient details hXD htX hCQ hZD
  exact exists_ne_one_mem_W_of_mulEquiv _ _ φ hH hD
    (hyp.exists_ne_one_mem_residualQuotientHypothesis_W details)

/-! ### `C_Q(D) = 1` on `U/Z(U)`

The standard model has it (`rootHom_range_inf_centralizer_psuTorus_eq_bot`), and it is an
isomorphism invariant of the pair `(Q, D)` (`inf_centralizer_eq_bot_of_mulEquiv`), so it
travels first to the transported standing hypothesis and then, along the matching of
`exists_mulEquiv_match_residualQuotient`, to the intrinsic one.  It is the extra input of
`Setup.mul_mem_K_of_setup`, i.e. of the matching of the distinguished involutions. -/

/-- **`C_Q(D) = 1` for the transported standing hypothesis on `U/Z(U)`.** -/
theorem inf_centralizer_residualQuotientHypothesis
    (details : CentralizerPSUData hyp X result data) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    (hyp.residualQuotientHypothesis details).Q ⊓ Subgroup.centralizer
        (((hyp.residualQuotientHypothesis details).D : Set (↥(residual (G := G) X) ⧸
          Subgroup.center ↥(residual (G := G) X)))) = ⊥ := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  have hstd : (standardHypothesis data.n data.one_lt_n).Q ⊓ Subgroup.centralizer
      (((standardHypothesis data.n data.one_lt_n).D : Set (standardPermGroup data.n))) = ⊥ :=
    rootHom_range_inf_centralizer_psuTorus_eq_bot data.one_lt_n
  have hlift := inf_centralizer_eq_bot_of_mulEquiv (MulEquiv.refl (standardPermGroup data.n))
    (Q := (standardHypothesis data.n data.one_lt_n).Q)
    (D := (standardHypothesis data.n data.one_lt_n).D) rfl rfl hstd
  exact inf_centralizer_eq_bot_of_mulEquiv details.residualQuotientEquiv.symm rfl rfl hlift

/-- **`C_Q̄(D̄) = 1` for the intrinsic standing hypothesis on `U/Z(U)`.** -/
theorem inf_centralizer_intrinsicResidualQuotient
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q ⊓ Subgroup.centralizer
        (((hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).D :
          Set (↥(residualImage (G := G) X) ⧸
            Subgroup.center ↥(residualImage (G := G) X)))) = ⊥ := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  obtain ⟨φ, _hH, hQ, hD⟩ :=
    hyp.exists_mulEquiv_match_residualQuotient details hXD htX hCQ hZD
  exact inf_centralizer_eq_bot_of_mulEquiv φ hQ hD
    (hyp.inf_centralizer_residualQuotientHypothesis details)

/-- **🎯 The intrinsic and transported standing hypotheses on `U/Z(U)` are matched on all
four of `H`, `Q`, `D` and `t`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133).

`exists_mulEquiv_match_residualQuotient` matches the first three; the two distinguished
involutions then differ by an element of `K` (`Setup.mul_mem_K_of_setup`, using
`C_Q̄(D̄) = 1`), and conjugating by `K` realizes that difference
(`exists_mem_K_conj_t_eq`) without moving `H`, `Q` or `D`.

Every subgroup Part II attaches to a standing hypothesis — `Q₀`, `V`, `K`, `W`, the
distinguished pair — is built from these four, so all of them correspond. -/
theorem exists_mulEquiv_match_residualQuotient_t
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    ∃ ψ : (↥(residual (G := G) X) ⧸ Subgroup.center ↥(residual (G := G) X)) ≃*
        (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)),
      (hyp.residualQuotientHypothesis details).H.map ψ.toMonoidHom
          = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).H ∧
        (hyp.residualQuotientHypothesis details).Q.map ψ.toMonoidHom
          = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q ∧
        (hyp.residualQuotientHypothesis details).D.map ψ.toMonoidHom
          = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).D ∧
        ψ (hyp.residualQuotientHypothesis details).t
          = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).t := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  obtain ⟨φ, hH, hQ, hD⟩ :=
    hyp.exists_mulEquiv_match_residualQuotient details hXD htX hCQ hZD
  set hi := hyp.intrinsicResidualQuotient details hXD htX hCQ hZD with hidef
  have hSφ : OddOrder.GroupTheory.RankOneBNPair.Setup hi.H hi.Q hi.D
      (φ (hyp.residualQuotientHypothesis details).t) := by
    have h := (hyp.residualQuotientHypothesis details).rankOneSetup.map φ
    rwa [hH, hQ, hD] at h
  have hK := hi.rankOneSetup.mul_mem_K_of_setup hSφ
    (hyp.inf_centralizer_intrinsicResidualQuotient details hXD htX hCQ hZD)
  have hmemK : φ (hyp.residualQuotientHypothesis details).t * hi.t ∈ hi.K := by
    rw [← SetLike.mem_coe, hi.coe_K]
    exact ⟨hK.1, hK.2⟩
  obtain ⟨e, heK, he⟩ := hi.exists_mem_K_conj_t_eq hmemK
  have heD : e ∈ hi.D := hi.K_le_D heK
  have heM : e ∈ hi.H := hi.D_le_H heD
  have hcomp : (φ.trans (MulAut.conj e)).toMonoidHom
      = (MulAut.conj e).toMonoidHom.comp φ.toMonoidHom := by ext x; rfl
  have hQe : hi.Q.map (MulAut.conj e).toMonoidHom = hi.Q := by
    refine le_antisymm ?_ fun x hx => ⟨e⁻¹ * x * e, hi.rankOneSetup.conj_mem_Q heM hx, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have h := hi.rankOneSetup.conj_mem_Q (hi.H.inv_mem heM) hx
      simpa using h
    · change e * (e⁻¹ * x * e) * e⁻¹ = x
      group
  have htt : hi.t * hi.t = 1 := by rw [← sq]; exact hi.t_sq
  have hteq : e⁻¹ * hi.t * e = φ (hyp.residualQuotientHypothesis details).t := by
    rw [he, mul_assoc, htt, mul_one]
  refine ⟨φ.trans (MulAut.conj e), ?_, ?_, ?_, ?_⟩
  · rw [hcomp, ← Subgroup.map_map, hH]; exact map_conj_self heM
  · rw [hcomp, ← Subgroup.map_map, hQ]; exact hQe
  · rw [hcomp, ← Subgroup.map_map, hD]; exact map_conj_self heD
  · change e * φ (hyp.residualQuotientHypothesis details).t * e⁻¹ = hi.t
    rw [← hteq]
    group

/-- **🎯 `V̄ = W̄` for the intrinsic standing hypothesis on `U/Z(U)`** —
`corollaryTwo_of_standardModel`'s `hVW`.

`V` is determined by `D` and `t`, `W` by `H` and `D`, and
`exists_mulEquiv_match_residualQuotient_t` matches all four, so `V = W` transports from
the transported hypothesis (`residualQuotientHypothesis_V_eq_W`). -/
theorem V_eq_W_intrinsicResidualQuotient (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).V
      = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).W := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  obtain ⟨ψ, hH, _hQ, hD, ht⟩ :=
    hyp.exists_mulEquiv_match_residualQuotient_t details hXD htX hCQ hZD
  have hV := map_V_of_mulEquiv (hyp.residualQuotientHypothesis details)
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD) ψ hD ht
  have hW := map_W_of_mulEquiv (hyp.residualQuotientHypothesis details)
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD) ψ hH hD
  rw [← hV, ← hW, hyp.residualQuotientHypothesis_V_eq_W details]

/-! ### Moving the point set into `Ω`'s universe

The ambient induction hypothesis `TheoremAInductionBelow G Ω` quantifies over permuted
sets in `Ω`'s universe, so a standing hypothesis it can be applied below must have its
permuted set there.  The intrinsic one permutes `L̄ ⧸ M̄`, which lives in `G`'s universe;
but Ch. IV §1's identification `L̄ ⧸ M̄ ≅ Q̄ ∪ {a}` (`coordsEquiv`) together with
`Q̄ ≅ RootGroup ℓ` puts it in bijection with the standard `Unital ℓ`, a small type, which
lifts anywhere.  `ofRankOneSetupOfEquiv` then reads the same hypothesis there. -/

/-- **The point set of the intrinsic action is the standard `Unital ℓ`** — `L̄ ⧸ M̄` is
`Q̄ ∪ {a}` (Ch. IV §1, p. 123) and `Q̄ ≅ C_Q(X) ≅ RootGroup ℓ` (Ch. I §3 Prop 1(c)). -/
noncomputable def intrinsicPointEquiv (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    ((↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)) ⧸
        (hyp.H.subgroupOf (residualImage (G := G) X)).map
          (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      ≃ Unital data.n :=
  (coordsEquiv (hyp.setup_residualQuotient hXD htX hCQ hZD)).symm.trans
    (Equiv.optionCongr
      ((hyp.cQMulEquivMapQ hXD htX hCQ hZD).symm.trans details.cQEquivRoot).toEquiv)

/-- **The intrinsic standing hypothesis on `U/Z(U)`, permuting `Unital ℓ`** — the same
`H`, `Q`, `D`, `t` as `intrinsicResidualQuotient`, with the point set relabelled so that
it lies in `Ω`'s universe. -/
noncomputable abbrev intrinsicPointEquivULift
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    ((↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X)) ⧸
        (hyp.H.subgroupOf (residualImage (G := G) X)).map
          (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))))
      ≃ ULift.{v} (Unital data.n) :=
  (hyp.intrinsicPointEquiv details hXD htX hCQ hZD).trans Equiv.ulift.symm

noncomputable def intrinsicResidualQuotientULift
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    letI := Hypothesis.rankOneSetupAction
      (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
    Hypothesis (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X))
      (ULift.{v} (Unital data.n)) :=
  letI := hyp.isSimpleGroup_residualQuotient details
  Hypothesis.ofRankOneSetupOfEquiv (hyp.setup_residualQuotient hXD htX hCQ hZD)
    (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
    (hyp.setup_residualQuotient hXD htX hCQ hZD).normalCore_eq_bot_of_isSimpleGroup
    (hyp.even_natCard_map_Q_residualQuotient details hXD htX hCQ hZD)
    hyp.odd_natCard_map_D_residualQuotient
    (hyp.two_rank_ge_two_residualQuotient details)

/-- The four structural fields agree with those of `intrinsicResidualQuotient`: relabelling
the point set does not move them (`ofRankOneSetupOfEquiv_*`). -/
theorem intrinsicResidualQuotientULift_H (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    letI := Hypothesis.rankOneSetupAction
      (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
    (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).H
      = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).H := by
  letI := Hypothesis.rankOneSetupAction
    (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
  exact ofRankOneSetupOfEquiv_H _ _ _ _ _ _

theorem intrinsicResidualQuotientULift_Q (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    letI := Hypothesis.rankOneSetupAction
      (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
    (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).Q
      = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q := by
  letI := Hypothesis.rankOneSetupAction
    (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
  exact ofRankOneSetupOfEquiv_Q _ _ _ _ _ _

theorem intrinsicResidualQuotientULift_D (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    letI := Hypothesis.rankOneSetupAction
      (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
    (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).D
      = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).D := by
  letI := Hypothesis.rankOneSetupAction
    (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
  exact ofRankOneSetupOfEquiv_D _ _ _ _ _ _

theorem intrinsicResidualQuotientULift_t (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X)) :
    letI := Hypothesis.rankOneSetupAction
      (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
    (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).t
      = (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).t := rfl

/-- **The induction hypothesis restricts to `U/Z(U)`** with the intrinsic point set.

`TheoremAInductionBelow` only looks at the order of the group, so this is `ih` composed
with `natCard_residualImageQuotient_lt`; what makes it typecheck at all is that the
permuted set has been moved into `Ω`'s universe. -/
theorem theoremAInductionBelow_intrinsicResidualQuotient
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X))
    (hXV : X ≤ hyp.V) (hX : X ≠ ⊥) (ih : TheoremAInductionBelow G Ω) :
    letI := Hypothesis.rankOneSetupAction
      ((hyp.intrinsicPointEquiv details hXD htX hCQ hZD).trans Equiv.ulift.symm)
    TheoremAInductionBelow
      (↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X))
      (ULift.{v} (Unital data.n)) := by
  letI := Hypothesis.rankOneSetupAction
    ((hyp.intrinsicPointEquiv details hXD htX hCQ hZD).trans Equiv.ulift.symm)
  intro A Λ _ _ _ hlt hA
  exact ih (hlt.trans (hyp.natCard_residualImageQuotient_lt hXV hX)) hA

/-- **🎯 Ch. I §3 Lemma 5 and the field model of Ch. III §3 hold for the *intrinsic*
standing hypothesis on `U/Z(U)`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133).

All seven inputs are now available: the three orders and the Suzuki `2`-group property
((118)), `|s̄ t̄| = 3` ((120)), the induction hypothesis, and `1 ≠ w ∈ W̄`.  The point set
is the relabelled `ULift (Unital ℓ)`, which is where the ambient induction hypothesis can
be applied; the structural fields are unchanged. -/
theorem nonempty_standingData_intrinsicResidualQuotient (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X))
    (ih : TheoremAInductionBelow G Ω) :
    letI := Hypothesis.rankOneSetupAction
      (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
    Nonempty ((hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).LemmaFiveSetup
        data.n) ∧
      Nonempty ((hyp.intrinsicResidualQuotientULift details hXD htX hCQ
        hZD).QuotientFieldModel data.n) := by
  letI := Hypothesis.rankOneSetupAction
    (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
  have hH := hyp.intrinsicResidualQuotientULift_H details hXD htX hCQ hZD
  have hQ := hyp.intrinsicResidualQuotientULift_Q details hXD htX hCQ hZD
  have hD := hyp.intrinsicResidualQuotientULift_D details hXD htX hCQ hZD
  have ht := hyp.intrinsicResidualQuotientULift_t details hXD htX hCQ hZD
  have hW := W_eq_of_H_D_eq (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD)
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD) hH hD
  have hs := distinguishedInvolution_eq_of_eq
    (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD)
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD) hH hQ ht
  have hQ0 := Q0_eq_of_H_eq (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD)
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD) hH
  obtain ⟨w, hwW, hw1⟩ :=
    hyp.exists_ne_one_mem_W_intrinsicResidualQuotient details hXD htX hCQ hZD
  have hwW' : w ∈ (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).W := by
    rw [hW]; exact hwW
  have hst : orderOf
      ((hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).distinguishedInvolution *
        (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).t) = 3 := by
    rw [hs, ht]
    exact hyp.orderOf_distinguishedInvolution_mul_t_intrinsicResidualQuotient hXV common
      details hXD htX hCQ hZD
  have hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group
      ↥(hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).Q := by
    rw [hQ]
    exact hyp.isSuzuki2Group_Q_intrinsicResidualQuotient details hXD htX hCQ hZD
  have hn0 : data.n ≠ 0 := by have := data.one_lt_n; omega
  have hQ0card : Nat.card
      ↥(hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).Q0 = 2 ^ data.n := by
    rw [hQ0]
    exact hyp.natCard_Q0_intrinsicResidualQuotient hXV common details hXD htX hCQ hZD
  have hcardQ : Nat.card (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).Q
      = Nat.card ↥(hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).Q0 ^ 3 := by
    rw [hQ, hQ0]
    exact hyp.natCard_Q_intrinsicResidualQuotient hXV common details hXD htX hCQ hZD
  obtain ⟨sfive⟩ :=
    (hyp.intrinsicResidualQuotientULift details hXD htX hCQ
      hZD).lemmaFiveSetup_of_orderThree_of_mem_W hwW' hw1 hst hQsuz hn0 hQ0card hcardQ
      (hyp.theoremAInductionBelow_intrinsicResidualQuotient details hXD htX hCQ hZD hXV hX ih)
  exact ⟨⟨sfive⟩, (hyp.intrinsicResidualQuotientULift details hXD htX hCQ
    hZD).nonempty_quotientFieldModel_of_orderThree hst hQsuz hn0 hQ0card hcardQ
    (hyp.theoremAInductionBelow_intrinsicResidualQuotient details hXD htX hCQ hZD hXV hX ih)
    sfive hwW' hw1⟩

/-- **🎯 The Proposition of Ch. III §3 holds for the *intrinsic* standing hypothesis on
`U/Z(U)`** (Peterfalvi Part II, Ch. IV §4, step (2), p. 133).

This is what step (2) means by "running §2 and §3 relative to `U`": the model is obtained
for the hypothesis whose `H`, `Q`, `D`, `t` are the images of `U ∩ H`, `U ∩ Q`, `U ∩ D`
and `t`, so the mappings it constrains are the book's `f₁`, `h₁`. -/
theorem exists_isStandardModel_intrinsicResidualQuotient (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (common : CentralizerCommonData hyp X) (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X))
    (ih : TheoremAInductionBelow G Ω) :
    letI := Hypothesis.rankOneSetupAction
      (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
    ∃ (sfive : (hyp.intrinsicResidualQuotientULift details hXD htX hCQ
          hZD).LemmaFiveSetup data.n)
      (Mq : (hyp.intrinsicResidualQuotientULift details hXD htX hCQ
          hZD).QuotientFieldModel data.n)
      (x₀ : ↥(Subgroup.center (hyp.intrinsicResidualQuotientULift details hXD htX hCQ
          hZD).Q)), x₀ ≠ 1 ∧
      Nat.card ↥(hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).actualKActor
          = 2 ^ data.n - 1 ∧
      (hyp.intrinsicResidualQuotientULift details hXD htX hCQ
        hZD).IsStandardModel sfive Mq x₀ := by
  letI := Hypothesis.rankOneSetupAction
    (hyp.intrinsicPointEquivULift details hXD htX hCQ hZD)
  obtain ⟨⟨sfive⟩, ⟨Mq⟩⟩ := hyp.nonempty_standingData_intrinsicResidualQuotient hXV hX
    common details hXD htX hCQ hZD ih
  obtain ⟨x₀, hx₀⟩ :=
    (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).exists_center_Q_ne_one
  have hH := hyp.intrinsicResidualQuotientULift_H details hXD htX hCQ hZD
  have hQ := hyp.intrinsicResidualQuotientULift_Q details hXD htX hCQ hZD
  have ht := hyp.intrinsicResidualQuotientULift_t details hXD htX hCQ hZD
  have hs := distinguishedInvolution_eq_of_eq
    (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD)
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD) hH hQ ht
  have hQ0 := Q0_eq_of_H_eq (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD)
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD) hH
  have hst : orderOf
      ((hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).distinguishedInvolution *
        (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).t) = 3 := by
    rw [hs, ht]
    exact hyp.orderOf_distinguishedInvolution_mul_t_intrinsicResidualQuotient hXV common
      details hXD htX hCQ hZD
  have hn0 : data.n ≠ 0 := by have := data.one_lt_n; omega
  have hQ0card : Nat.card
      ↥(hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).Q0 = 2 ^ data.n := by
    rw [hQ0]
    exact hyp.natCard_Q0_intrinsicResidualQuotient hXV common details hXD htX hCQ hZD
  have hcardQ : Nat.card (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).Q
      = Nat.card ↥(hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).Q0 ^ 3 := by
    rw [hQ, hQ0]
    exact hyp.natCard_Q_intrinsicResidualQuotient hXV common details hXD htX hCQ hZD
  exact ⟨sfive, Mq, x₀, hx₀,
    (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).card_actualKActor_eq
      sfive Mq hn0 hQ0card,
    (hyp.intrinsicResidualQuotientULift details hXD htX hCQ hZD).exists_standardModel sfive
      Mq hst hn0 hQ0card hcardQ
      (hyp.theoremAInductionBelow_intrinsicResidualQuotient details hXD htX hCQ hZD hXV hX ih)
      x₀ hx₀⟩

end Model

/-! ### §2 and §3 run outright on `C/𝒩(C)`

`PSU3SectionFourSetup.standingData_centralizerQuotient` supplies both standing bundles and
all the numerics for `centralizerQuotientHypothesis`; the induction hypothesis restricts
along `theoremAInductionBelow_centralizerActionQuotient` and the central `x₀ ≠ 1` is
generic.  So the Proposition of Ch. III §3 holds there with no residual hypothesis, which
is what step (2) applies before reading its conclusion back into `C_G(P)` along the two
transfers above. -/

namespace SectionFourSetup

variable {hyp} (s4 : hyp.SectionFourSetup)

/-- **The Proposition of Ch. III §3 holds on `C/𝒩(C)`** (Peterfalvi Part II, Ch. IV §4,
step (2), p. 133). -/
theorem isStandardModel_centralizerQuotient {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu)
    (hQsuz : OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥hyp.Q)
    (hCop : Nat.Coprime (Nat.card ↥(s4.P.subgroupOf hyp.D)) (Nat.card ↥hyp.Q))
    (hSolv : IsSolvable ↥hyp.Q) (hP : s4.P ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer ((s4.P : Set G))),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hord : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (ih : TheoremAInductionBelow G Ω) :
    letI := hyp.centralizerQuotientMulAction s4.P_le_V
    ∃ (n : ℕ) (sfive : (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).LemmaFiveSetup n)
      (Mq : (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).QuotientFieldModel n)
      (x₀ : ↥(Subgroup.center (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).Q)),
      n ≠ 0 ∧ x₀ ≠ 1 ∧ Nat.card ↥(hyp.centralizerQuotientHypothesis s4.P_le_V hA3).Q0 = 2 ^ n ∧
        Nat.card (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).Q
          = Nat.card ↥(hyp.centralizerQuotientHypothesis s4.P_le_V hA3).Q0 ^ 3 ∧
        orderOf
            ((hyp.centralizerQuotientHypothesis s4.P_le_V hA3).distinguishedInvolution *
              (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).t) = 3 ∧
        Function.Injective Mq.mu ∧
        (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).IsStandardModel sfive Mq x₀ := by
  letI := hyp.centralizerQuotientMulAction s4.P_le_V
  obtain ⟨n, hn, hQ0card, hcardQ, hst, _hQsuzBar, ⟨sfive⟩, ⟨Mq⟩⟩ :=
    s4.standingData_centralizerQuotient M hZ hmu hQsuz hCop hSolv hP hA3 hord ih
  obtain ⟨x₀, hx₀⟩ :=
    (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).exists_center_Q_ne_one
  exact ⟨n, sfive, Mq, x₀, hn, hx₀, hQ0card, hcardQ, hst,
    (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).mu_injective hst hn hQ0card hcardQ
      (hyp.theoremAInductionBelow_centralizerActionQuotient s4.P_le_V hP ih) sfive Mq,
    (hyp.centralizerQuotientHypothesis s4.P_le_V hA3).exists_standardModel sfive Mq hst hn
      hQ0card hcardQ (hyp.theoremAInductionBelow_centralizerActionQuotient s4.P_le_V hP ih)
      x₀ hx₀⟩

end SectionFourSetup


end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
