/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaSix
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.GroupTheory.RepresentationTheory.CyclicExtension

/-!
# Higman's Lemma 6: the triple-bracket contradiction

This file assembles the lower-central square formula, pair-weight spectrum,
triple-bracket fiber elimination, and the full-span contradiction from
G. Higman, *Suzuki 2-groups*, Lemma 6, pp. 85--86.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open Module
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open scoped BigOperators IsMulCommutative TensorProduct

universe uF uK uC uV uW uH

local instance instTripleBracketConclusionLayerIsMulCommutative
    (H : Type uH) [Group H] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  ⟨⟨(lowerCentralLayer_isElementaryAbelian H i).1⟩⟩

noncomputable local instance instTripleBracketConclusionLayerZModTwoModule
    (H : Type uH) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-! ## Faithfulness of the effective odd-order actor -/

/-- For every finite `2`-group, the ambient denominator of Higman's first
lower-central layer is exactly the Frattini subgroup. -/
theorem lowerCentralLayerKernelInAmbient_zero_eq_frattini
    (H : Type uH) [Group H] [Finite H] (hH : IsPGroup 2 H) :
    lowerCentralLayerKernelInAmbient H 0 = frattini H := by
  have hAgemo :
      Agemo H 2 1 = Subgroup.closure (Set.range fun x : H => x ^ 2) := by
    simp only [Agemo, pow_one]
    congr 1
    ext x
    simp [eq_comm]
  have hLower : lowerCentralTerm H 1 = _root_.commutator H := by
    rw [lowerCentralTerm, Subgroup.top_lowerCentralSeries_one]
  rw [lowerCentralLayerKernelInAmbient_eq,
    agemo_lowerCentralTerm_zero_map_eq, hLower, hAgemo, sup_comm]
  exact OddOrder.BG.Ch1.S01.commutator_sup_pow_closure_eq_frattini hH

/-- Triviality on the first lower-central representation gives pointwise
triviality modulo the Frattini subgroup. -/
private theorem layerZero_action_trivial_gives_frattini_coset
    {H : Type uH} {C : Type uC} [Group H] [Finite H] [Group C]
    (phi : C →* MulAut H)
    (hH : IsPGroup 2 H)
    (c : C)
    (hc : lowerCentralLayerRepresentation phi 0 c = 1) :
    ∀ g : H, ∃ x ∈ _root_.frattini H, (phi c) g = g * x := by
  intro g
  let g₀ : ↥(lowerCentralTerm H 0) :=
    ⟨g, by simp [lowerCentralTerm]⟩
  let q : lowerCentralLayer H 0 :=
    QuotientGroup.mk' (lowerCentralLayerKernel H 0) g₀
  have hlin :
      lowerCentralLayerRepresentation phi 0 c (Additive.ofMul q) =
        Additive.ofMul q := by
    rw [hc]
    rfl
  have hq : lowerCentralLayerAction phi 0 c q = q := by
    apply Additive.ofMul.injective
    simpa only [lowerCentralLayerRepresentation_apply] using hlin
  have hq' :
      QuotientGroup.mk' (lowerCentralLayerKernel H 0) g₀ =
        QuotientGroup.mk' (lowerCentralLayerKernel H 0)
          (lowerCentralTermAction phi 0 c g₀) := by
    simpa only [q, lowerCentralLayerAction_apply_mk] using hq.symm
  obtain ⟨x₀, hx₀, hgx⟩ :=
    (QuotientGroup.mk'_eq_mk'
      (N := lowerCentralLayerKernel H 0)).mp hq'
  refine ⟨(x₀ : H), ?_, ?_⟩
  · rw [← lowerCentralLayerKernelInAmbient_zero_eq_frattini H hH]
    exact ⟨x₀, hx₀, rfl⟩
  · exact (congrArg Subtype.val hgx).symm

/-- A faithful odd-order automorphism group of a finite `2`-group acts
faithfully on Higman's first lower-central layer.

The layer denominator is the Frattini subgroup.  An actor in the kernel
therefore acts trivially on the Frattini quotient.  Burnside's operator
theorem makes the corresponding coprime automorphism of `H` trivial, and
faithfulness of the ambient action then makes the actor itself trivial. -/
theorem lowerCentralLayerZeroRepresentation_injective_of_odd_faithful_action
    {H C : Type uH} [Group H] [Finite H] [CommGroup C] [Finite C]
    (hH : IsPGroup 2 H)
    (phi : C →* MulAut H)
    (hphi : Function.Injective phi)
    (hCodd : Odd (Nat.card C)) :
    Function.Injective (lowerCentralLayerRepresentation phi 0) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro c hc
  change lowerCentralLayerRepresentation phi 0 c = 1 at hc
  have hphiOrderOdd : Odd (orderOf (phi c)) :=
    hCodd.of_dvd_nat
      ((orderOf_map_dvd phi c).trans (orderOf_dvd_natCard c))
  have hphiOne : phi c = 1 :=
    OddOrder.BG.Ch1.S01.mulAut_eq_one_of_coprime_orderOf_of_frattini
      hH (phi c) (Nat.coprime_two_right.mpr hphiOrderOdd) (by
        intro z g
        have hcz : lowerCentralLayerRepresentation phi 0 (c ^ z) = 1 := by
          have hcKer : c ∈ (lowerCentralLayerRepresentation phi 0).ker := hc
          exact (lowerCentralLayerRepresentation phi 0).ker.zpow_mem hcKer z
        simpa only [map_zpow] using
          layerZero_action_trivial_gives_frattini_coset
            phi hH (c ^ z) hcz g)
  apply hphi
  simpa only [map_one] using hphiOne

/-! ## The Lemma 4 contradiction for a nonfaithful actor -/

/-- Higman's Lemma 4 does not require the displayed cyclic actor to act
faithfully on either layer.  If an equivariant equivalence existed, then
transitivity on the second layer would transport to the first.  Singer
coordinates may therefore be constructed through the faithful effective
image of the first-layer representation.

This is the source-strength form needed later in Lemma 7, where restriction
of the ambient actor to a normal invariant cover need not be injective. -/
theorem not_exists_equivariant_linearEquiv_of_higman_bracket_of_transitive
    {C V₁ V₂ : Type uH}
    [CommGroup C] [IsCyclic C] [Finite C]
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [Finite V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [Finite V₂]
    (rho₁ : Representation (ZMod 2) C V₁)
    (rho₂ : Representation (ZMod 2) C V₂)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin₂ : Module.finrank (ZMod 2) V₂ = n)
    (beta : LinearMap.BilinMap (ZMod 2) V₁ V₂)
    (hbetaEquiv : ∀ c x y,
      rho₂ c (beta x y) = beta (rho₁ c x) (rho₁ c y))
    (hbetaAlt : ∀ x, beta x x = 0)
    (hbetaSpan : Submodule.span (ZMod 2)
      (Set.range fun z : V₁ × V₁ => beta z.1 z.2) = ⊤)
    (htrans₂ : ∀ v w : V₂, v ≠ 0 → w ≠ 0 →
      ∃ c : C, rho₂ c v = w) :
    ¬ ∃ e : V₁ ≃ₗ[ZMod 2] V₂,
      ∀ c v, e (rho₁ c v) = rho₂ c (e v) := by
  classical
  rintro ⟨e, he⟩
  have hfin₁ : Module.finrank (ZMod 2) V₁ = n :=
    e.finrank_eq.trans hfin₂
  letI : Nontrivial V₂ :=
    Module.nontrivial_of_finrank_pos (by rw [hfin₂]; omega)
  letI : Nontrivial V₁ := e.toEquiv.nontrivial
  have htrans₁ : ∀ v w : V₁, v ≠ 0 → w ≠ 0 →
      ∃ c : C, rho₁ c v = w := by
    intro v w hv hw
    obtain ⟨c, hc⟩ := htrans₂ (e v) (e w)
      (e.map_ne_zero_iff.mpr hv) (e.map_ne_zero_iff.mpr hw)
    refine ⟨c, e.injective ?_⟩
    rw [he]
    exact hc
  obtain ⟨c, hcgen⟩ := IsCyclic.exists_generator (α := C)
  let K := GaloisField 2 n
  obtain ⟨_efield, lambda, b, hprim, _hconj, _hgen, hb⟩ :=
    exists_singerFrobeniusEigenbasis_of_transitive_generator
      rho₁ n hn hfin₁ htrans₁ c hcgen
  let betaK : LinearMap.BilinMap K
      (K ⊗[ZMod 2] V₁) (K ⊗[ZMod 2] V₂) :=
    beta.baseChange K
  let T₁ : Module.End K (K ⊗[ZMod 2] V₁) := (rho₁ c).baseChange K
  let T₂ : Module.End K (K ⊗[ZMod 2] V₂) := (rho₂ c).baseChange K
  have hbetaEquivK : ∀ x y,
      T₂ (betaK x y) = betaK (T₁ x) (T₁ y) := by
    intro x y
    exact LinearMap.BilinMap.baseChange_equivariant
      beta (rho₁ c) (rho₂ c) (hbetaEquiv c) x y
  have hbetaAltK : ∀ x, betaK x x = 0 := by
    intro x
    exact LinearMap.BilinMap.zmodTwo_baseChange_self_eq_zero beta hbetaAlt x
  have hbetaSpanK : Submodule.span K
      (Set.range fun z : (K ⊗[ZMod 2] V₁) × (K ⊗[ZMod 2] V₁) =>
        betaK z.1 z.2) = ⊤ :=
    LinearMap.BilinMap.baseChange_span_eq_top beta hbetaSpan
  have hpairSpan : ⨆ mu ∈ Set.range (fun p : HigmanExponentPair n ↦
      lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)),
      T₂.eigenspace mu = ⊤ :=
    iSup_frobeniusPairWeight_eigenspace_eq_top_of_bilinear
      n lambda T₁ T₂ b hb betaK hbetaEquivK hbetaAltK hbetaSpanK
  let i₀ : Fin n := ⟨0, by omega⟩
  have hfirst : T₁ (b i₀) = lambda • b i₀ := by
    simpa [i₀] using hb i₀
  have hsecond : T₂
      (e.baseChange (ZMod 2) K V₁ V₂ (b i₀)) =
      lambda • (e.baseChange (ZMod 2) K V₁ V₂ (b i₀)) :=
    baseChange_eigenvector_equation_of_equivariant_linearEquiv
      rho₁ rho₂ e he c lambda (b i₀) hfirst
  have hsecondNe : e.baseChange (ZMod 2) K V₁ V₂ (b i₀) ≠ 0 :=
    (e.baseChange (ZMod 2) K V₁ V₂).map_ne_zero_iff.mpr (b.ne_zero i₀)
  have hlambda : T₂.HasEigenvalue lambda :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hsecond, hsecondNe⟩
  exact higman_spectral_contradiction T₂ n hn lambda hprim hpairSpan hlambda

/-- An equivariant linear equivalence transports a displayed family of
eigenspaces which spans after scalar extension. -/
private theorem eigenspaces_iSup_eq_top_of_equivariant_linearEquiv
    {F : Type uF} {K : Type uK} {C : Type uC}
    {V : Type uV} {W : Type uW}
    [Field F] [Field K] [Algebra F K] [Group C]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (rhoV : Representation F C V) (rhoW : Representation F C W)
    (e : V ≃ₗ[F] W)
    (he : ∀ c v, e (rhoV c v) = rhoW c (e v))
    (c : C) {κ : Type*} (weight : κ → K)
    (hspan : ⨆ mu ∈ Set.range weight,
      Module.End.eigenspace
        (((rhoV c).baseChange K) : Module.End K (K ⊗[F] V)) mu = ⊤) :
    ⨆ mu ∈ Set.range weight,
      Module.End.eigenspace
        (((rhoW c).baseChange K) : Module.End K (K ⊗[F] W)) mu = ⊤ := by
  let eK : K ⊗[F] V ≃ₗ[K] K ⊗[F] W := e.baseChange F K V W
  let S : Submodule K (K ⊗[F] W) :=
    ⨆ mu ∈ Set.range weight,
      Module.End.eigenspace
        (((rhoW c).baseChange K) : Module.End K (K ⊗[F] W)) mu
  apply top_unique
  intro w _
  obtain ⟨v, rfl⟩ := eK.surjective w
  have hvTop : v ∈ (⨆ mu ∈ Set.range weight,
      Module.End.eigenspace
        (((rhoV c).baseChange K) : Module.End K (K ⊗[F] V)) mu) := by
    rw [hspan]
    exact Submodule.mem_top
  have hle : (⨆ mu ∈ Set.range weight,
      Module.End.eigenspace
        (((rhoV c).baseChange K) : Module.End K (K ⊗[F] V)) mu) ≤
        S.comap eK.toLinearMap := by
    apply iSup_le
    intro mu
    apply iSup_le
    intro hmu x hx
    change eK x ∈ S
    apply Submodule.mem_iSup_of_mem mu
    apply Submodule.mem_iSup_of_mem hmu
    apply Module.End.mem_eigenspace_iff.mpr
    exact baseChange_eigenvector_equation_of_equivariant_linearEquiv
      rhoV rhoW e he c mu x (Module.End.mem_eigenspace_iff.mp hx)
  exact hle hvTop

/-- If an alternating symmetric bilinear map spans the middle space, then
vanishing of the composed map on increasing basis triples makes the second
bilinear map identically zero. -/
private theorem secondBilinear_eq_zero_of_basis_triples
    {K : Type uK} [Field K]
    {V : Type uV} {W : Type uW} {X : Type*}
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X]
    (n : ℕ) (b : Basis (Fin n) K V)
    (beta : LinearMap.BilinMap K V W)
    (hbetaSymm : ∀ x y, beta x y = beta y x)
    (hbetaSelf : ∀ x, beta x x = 0)
    (hbetaSpan : Submodule.span K
      (Set.range fun z : V × V => beta z.1 z.2) = ⊤)
    (gamma : W →ₗ[K] V →ₗ[K] X)
    (hzero : ∀ (p : HigmanExponentPair n) (k : Fin n),
      gamma (beta (b p.1.1) (b p.1.2)) (b k) = 0) :
    gamma = 0 := by
  let tau : V →ₗ[K] V →ₗ[K] V →ₗ[K] X :=
    { toFun := fun x => gamma.comp (beta x)
      map_add' := by
        intro x y
        ext z w
        simp
      map_smul' := by
        intro a x
        ext z w
        simp }
  have htau : tau = 0 := by
    apply Module.Basis.ext b
    intro i
    apply Module.Basis.ext b
    intro j
    apply Module.Basis.ext b
    intro k
    change gamma (beta (b i) (b j)) (b k) = 0
    rcases lt_trichotomy i j with hij | hij | hij
    · let p : HigmanExponentPair n := ⟨(i, j), hij⟩
      exact hzero p k
    · subst j
      rw [hbetaSelf]
      simp
    · let p : HigmanExponentPair n := ⟨(j, i), hij⟩
      rw [hbetaSymm]
      exact hzero p k
  have hle : Submodule.span K
      (Set.range fun z : V × V => beta z.1 z.2) ≤ LinearMap.ker gamma := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change gamma (beta x y) = 0
    change tau x y = 0
    rw [htau]
    rfl
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rwa [← hbetaSpan]

/-- The triple-bracket contradiction in the faithful-first-layer
specialization used by the source-facing form of **Higman Lemma 6**.

Assume H squared is H₂, the cyclic actor is faithful and irreducible on L₁,
and transitive on the nonzero vectors of L₂, where dim L₂ = n ≥ 2.
Then L₂ and L₃ are not equivariantly linearly equivalent. -/
theorem not_exists_equivariant_linearEquiv_of_higman_tripleBracket_of_faithful_firstLayer
    {H C : Type uH} [Group H] [Finite H]
    [CommGroup C] [IsCyclic C] [Finite C]
    (phi : C →* MulAut H)
    (hAgemo : Agemo H 2 1 = lowerCentralTerm H 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin₂ : Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer H 1)) = n)
    (hirr₁ : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (hfaith₁ : Function.Injective
      (lowerCentralLayerRepresentation phi 0))
    (htrans₂ : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ c : C,
        lowerCentralLayerRepresentation phi 1 c v = w) :
    ¬ ∃ e : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2]
        Additive (lowerCentralLayer H 2),
      ∀ c v,
        e (lowerCentralLayerRepresentation phi 1 c v) =
          lowerCentralLayerRepresentation phi 2 c (e v) := by
  classical
  letI : Nontrivial (Additive (lowerCentralLayer H 1)) :=
    Module.nontrivial_of_finrank_pos (by rw [hfin₂]; omega)
  rintro ⟨e, hequiv⟩
  have hfin₁ : Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer H 0)) = n :=
    (lowerCentralLayerZero_finrank_eq_one_of_equivariant_linearEquiv
      phi hirr₁ hfaith₁ htrans₂ e hequiv).trans hfin₂
  have hnodd : Odd n := by
    rw [← hfin₂]
    exact lowerCentralLayerOne_finrank_odd_of_equivariant_linearEquiv
      phi hAgemo hirr₁ hfaith₁ htrans₂ e hequiv
  have hn3 : 3 ≤ n := by
    rcases hnodd with ⟨d, hd⟩
    omega
  have hn0 : n ≠ 0 := by omega
  letI : NeZero n := ⟨hn0⟩
  have hfaith₂ : Function.Injective
      (lowerCentralLayerRepresentation phi 1) :=
    lowerCentralLayerOneRepresentation_injective_of_equivariant_linearEquiv
      phi hirr₁ hfaith₁ e hequiv
  have hirr₂ : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 1) :=
    representation_isIrreducible_of_transitive_nonzero
      (lowerCentralLayerRepresentation phi 1) htrans₂
  obtain ⟨c, hc⟩ :=
    exists_generator_orderOf_eq_pow_sub_one_of_faithful_transitive_nonzero
      (lowerCentralLayerRepresentation phi 1) n hfin₂ hfaith₂ htrans₂
  let K := GaloisField 2 n
  let hSq := lowerCentralSquaresLieInSecond_of_agemo_eq H hAgemo
  have hformula := exists_lowerCentralSquareMap_eq_frobeniusSum
    phi hAgemo n hn0 hfin₁ n hn hfin₂ hirr₁ hfaith₁ htrans₂
  dsimp only at hformula
  rw [GaloisField.finrank 2 hn0] at hformula
  obtain ⟨e₁, mu, b₁, hmu, _hcoord, hexpand, hb₁all, hsquare⟩ := hformula
  let lambda : K := (mu c : K)
  have hlambdaOrder : orderOf lambda = 2 ^ n - 1 := by
    exact orderOf_units.trans ((orderOf_injective mu hmu c).trans hc)
  have hprim : IsPrimitiveRoot lambda (2 ^ n - 1) :=
    IsPrimitiveRoot.iff_orderOf.mpr hlambdaOrder
  have hb₁ : ∀ i,
      (lowerCentralLayerRepresentation phi 0 c).baseChange K (b₁ i) =
        lambda ^ (2 ^ i.val) • b₁ i := by
    intro i
    exact hb₁all c i
  let x : Additive (lowerCentralLayer H 0) := e₁.symm 1
  have hex : e₁ x = 1 := e₁.apply_symm_apply 1
  have hx : (1 : K) ⊗ₜ[ZMod 2] x = ∑ i : Fin n, b₁ i := by
    rw [hexpand x, hex]
    simp
  have hq : lowerCentralSquareMapBaseChange K H hSq x =
      ∑ i : Fin n, ∑ j : Fin n with i < j,
        lowerCentralCommutatorBilinearBaseChange K H (b₁ i) (b₁ j) := by
    simpa only [K, hSq, hex, one_pow, one_smul] using hsquare x
  obtain ⟨_e₂, nu, b₂, _hprimNu, _hconj₂, _hgen₂, hb₂⟩ :=
    exists_singerFrobeniusEigenbasis_of_faithful_irreducible
      (lowerCentralLayerRepresentation phi 1) n hn hfin₂
      hirr₂ hfaith₂ c hc
  obtain ⟨p₀, _hnu, hsupport⟩ :=
    exists_lowerCentralPairGapSupport_of_frobeniusEigenbases
      K phi c hn lambda nu hprim b₁ hb₁ b₂ hb₂
  let r : ZMod n := higmanCyclicGap p₀.1.1 p₀.1.2
  let T₁ : Module.End K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) :=
    (lowerCentralLayerRepresentation phi 0 c).baseChange K
  let T₂ : Module.End K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 1)) :=
    (lowerCentralLayerRepresentation phi 1 c).baseChange K
  let T₃ : Module.End K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 2)) :=
    (lowerCentralLayerRepresentation phi 2 c).baseChange K
  let beta := lowerCentralCommutatorBilinearBaseChange K H
  let gamma := lowerCentralDegreeThreeCommutatorBilinearBaseChange K H
  have hbetaEquiv : ∀ u v, T₂ (beta u v) = beta (T₁ u) (T₁ v) := by
    intro u v
    exact lowerCentralCommutatorBilinearBaseChange_equivariant K phi c u v
  have hpairSpan₂ : ⨆ eta ∈ Set.range (fun p : HigmanExponentPair n ↦
      lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)), T₂.eigenspace eta = ⊤ :=
    iSup_frobeniusPairWeight_eigenspace_eq_top_of_bilinear
      n lambda T₁ T₂ b₁ hb₁ beta hbetaEquiv
      (lowerCentralCommutatorBilinearBaseChange_self K H)
      (lowerCentralCommutatorBilinearBaseChange_span_eq_top K H)
  have hpairSpan₃ : ⨆ eta ∈ Set.range (fun p : HigmanExponentPair n ↦
      lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)), T₃.eigenspace eta = ⊤ := by
    exact eigenspaces_iSup_eq_top_of_equivariant_linearEquiv
      (lowerCentralLayerRepresentation phi 1)
      (lowerCentralLayerRepresentation phi 2) e hequiv c
      (fun p : HigmanExponentPair n ↦
        lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)) hpairSpan₂
  have hsum : ∑ i : Fin n, ∑ j : Fin n with i < j, ∑ k : Fin n,
      gamma (beta (b₁ i) (b₁ j)) (b₁ k) = 0 :=
    lowerCentralTripleCommutator_sum_eq_zero_of_square_formula
      K H hSq b₁ x hx hq
  have hsupport' : ∀ i j : Fin n,
      beta (b₁ i) (b₁ j) ≠ 0 → HasHigmanPairGap r i j := by
    simpa only [beta, r] using hsupport
  have hzero : ∀ (q : HigmanExponentPair n) (k : Fin n),
      gamma (beta (b₁ q.1.1) (b₁ q.1.2)) (b₁ k) = 0 :=
    lowerCentralTripleCommutator_all_terms_eq_zero
      K phi c hn3 hnodd lambda hprim b₁ hb₁ hpairSpan₃
      r hsupport' hsum
  have hbetaSymm : ∀ u v, beta u v = beta v u := by
    intro u v
    unfold beta lowerCentralCommutatorBilinearBaseChange
    exact LinearMap.BilinMap.baseChange_isSymm
      (LinearMap.BilinMap.zmodTwo_symmetric_of_self_eq_zero
        (lowerCentralCommutatorBilinear H)
        (lowerCentralCommutatorBilinear_self H)) u v
  have hgammaZero : gamma = 0 :=
    secondBilinear_eq_zero_of_basis_triples n b₁ beta hbetaSymm
      (lowerCentralCommutatorBilinearBaseChange_self K H)
      (lowerCentralCommutatorBilinearBaseChange_span_eq_top K H)
      gamma hzero
  have hgammaSpan :=
    lowerCentralDegreeThreeCommutatorBilinearBaseChange_span_eq_top K H
  have hle : Submodule.span K
      (Set.range fun z :
          (K ⊗[ZMod 2] Additive (lowerCentralLayer H 1)) ×
            (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) =>
        gamma z.1 z.2) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    rw [hgammaZero]
    exact Submodule.zero_mem _
  change Submodule.span K
      (Set.range fun z :
          (K ⊗[ZMod 2] Additive (lowerCentralLayer H 1)) ×
            (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) =>
        gamma z.1 z.2) = ⊤ at hgammaSpan
  rw [hgammaSpan] at hle
  let eK : K ⊗[ZMod 2] Additive (lowerCentralLayer H 1) ≃ₗ[K]
      K ⊗[ZMod 2] Additive (lowerCentralLayer H 2) :=
    e.baseChange (ZMod 2) K _ _
  let i₀ : Fin n := ⟨0, by omega⟩
  have hwne : eK (b₂ i₀) ≠ 0 :=
    eK.map_ne_zero_iff.mpr (b₂.ne_zero i₀)
  apply hwne
  simpa only [Submodule.mem_bot] using (hle Submodule.mem_top)

/-- **Higman Lemma 6** (pp. 85--86), with the source hypotheses made
explicit.

Here `C` is the cyclic odd-order automorphism group itself: `phi` is a
faithful action on the finite `2`-group `H`.  Higman assumes irreducibility on
`L₁`, transitivity on `L₂#`, and `H² = H₂`; faithfulness on `L₁` is not an
extra hypothesis.  It follows from these source assumptions by the
Burnside--Frattini argument above.  Consequently `L₂` and `L₃` cannot be
equivariantly linearly equivalent. -/
theorem not_exists_equivariant_linearEquiv_of_higman_tripleBracket
    {H C : Type uH} [Group H] [Finite H]
    [CommGroup C] [IsCyclic C] [Finite C]
    (hH : IsPGroup 2 H)
    (phi : C →* MulAut H)
    (hphi : Function.Injective phi)
    (hCodd : Odd (Nat.card C))
    (hAgemo : Agemo H 2 1 = lowerCentralTerm H 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin₂ : Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer H 1)) = n)
    (hirr₁ : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (htrans₂ : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ c : C,
        lowerCentralLayerRepresentation phi 1 c v = w) :
    ¬ ∃ e : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2]
        Additive (lowerCentralLayer H 2),
      ∀ c v,
        e (lowerCentralLayerRepresentation phi 1 c v) =
          lowerCentralLayerRepresentation phi 2 c (e v) := by
  exact
    not_exists_equivariant_linearEquiv_of_higman_tripleBracket_of_faithful_firstLayer
      phi hAgemo n hn hfin₂ hirr₁
      (lowerCentralLayerZeroRepresentation_injective_of_odd_faithful_action
        hH phi hphi hCodd)
      htrans₂

/-- **Higman Lemma 6 for a possibly nonfaithful displayed actor.**

The action `phi` need not be injective.  Passing to its range gives a
faithful cyclic actor on `H`; its order remains odd because the range order
divides the order of `C`.  Irreducibility, transitivity, and the proposed
equivariant equivalence all descend along the surjection onto that range.

This is the form needed when an ambient automorphism subgroup is restricted
to a normal invariant cover. -/
theorem
    not_exists_equivariant_linearEquiv_of_higman_tripleBracket_of_odd_action
    {H C : Type uH} [Group H] [Finite H]
    [CommGroup C] [IsCyclic C] [Finite C]
    (hH : IsPGroup 2 H)
    (phi : C →* MulAut H)
    (hCodd : Odd (Nat.card C))
    (hAgemo : Agemo H 2 1 = lowerCentralTerm H 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin₂ : Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer H 1)) = n)
    (hirr₁ : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (htrans₂ : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ c : C,
        lowerCentralLayerRepresentation phi 1 c v = w) :
    ¬ ∃ e : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2]
        Additive (lowerCentralLayer H 2),
      ∀ c v,
        e (lowerCentralLayerRepresentation phi 1 c v) =
          lowerCentralLayerRepresentation phi 2 c (e v) := by
  classical
  let D := MonoidHom.range phi
  let psi : D →* MulAut H := D.subtype
  letI : Finite D := Finite.of_surjective phi.rangeRestrict
    phi.rangeRestrict_surjective
  letI : CommGroup D :=
    { (inferInstance : Group D) with
      mul_comm := by
        intro a b
        rcases a.2 with ⟨x, hx⟩
        rcases b.2 with ⟨y, hy⟩
        apply Subtype.ext
        change (a : MulAut H) * b = b * a
        rw [← hx, ← hy, ← map_mul, mul_comm, map_mul] }
  letI : IsCyclic D :=
    isCyclic_of_surjective phi.rangeRestrict
      phi.rangeRestrict_surjective
  have hcomp (i : ℕ) :
      (lowerCentralLayerRepresentation psi i).comp phi.rangeRestrict =
        lowerCentralLayerRepresentation phi i := by
    ext c q
    rfl
  have hirrD : Representation.IsIrreducible
      (lowerCentralLayerRepresentation psi 0) := by
    apply Representation.isIrreducible_of_isIrreducible_comp
      (f := phi.rangeRestrict) (lowerCentralLayerRepresentation psi 0)
    rw [hcomp]
    exact hirr₁
  have htransD : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ d : D,
        lowerCentralLayerRepresentation psi 1 d v = w := by
    intro v w hv hw
    obtain ⟨c, hc⟩ := htrans₂ v w hv hw
    exact ⟨phi.rangeRestrict c, hc⟩
  have hDodd : Odd (Nat.card D) :=
    hCodd.of_dvd_nat (Subgroup.card_range_dvd phi)
  rintro ⟨e, he⟩
  apply not_exists_equivariant_linearEquiv_of_higman_tripleBracket
    hH psi (Subgroup.subtype_injective D) hDodd hAgemo n hn hfin₂
    hirrD htransD
  refine ⟨e, ?_⟩
  intro d v
  obtain ⟨c, rfl⟩ := phi.rangeRestrict_surjective d
  exact he c v

end OddOrder.Higman.Suzuki2Groups
