# Peterfalvi (9.1) Wielandt fixed-point formula — proof design (lane-f, 2026-06-17)

## Status

- ✅ **Faithful redesign + corollaries DONE** (`CoprimeAction.lean`, commit `c55f6db2`,
  build-green + AxiomsCheck OK). 3 sorries → 1.
  - `CoprimeFrobeniusAction` now carries a real action `φ : L →* MulAut H`; the three
    fixed subgroups are *derived* (`fixedByUE/E/U = fixedSubgroup φ ⊤/E/U`), so the
    statements are genuine.
  - Both corollaries proved from the main formula (antitone fixed points +
    `Subgroup.eq_top_of_card_eq`).
- ✅ **I-1 abstract backbone COMPLETE** (2026-06-18, resume⁵): the Teichmüller-free orbit-count
  Brauer lemma is fully assembled at the abstract level — `CenterSimplesOrbit.exists_fixed_simple`
  (3d.3b), `card_simples_eq_card_classes` (N=Ncl), `FreeActionOrbitCount.dvd_card_sub_one_of_free_…`,
  `CenterOrbitFree.gamma_free_off_trivial_simple` (3d.3c). All sorry-free + axiom-clean. See resume⁵.
- ✅ **Abstract free-(†) ENGINE COMPLETE** (2026-06-18, resume⁵): `WielandtCounting`
  `finrank_eq_card_mul_finrank_invariants_of_free` (`FreeOrbitModuleCount.lean`) — `V = ⊕ Aᵢ`, `G`
  free on `ι` permuting summands ⟹ `dim V = |G|·dim Vᴳ` (sorry-free, axiom-clean). Plus I-4 core
  `Module.finrank_baseChange` confirmed in mathlib (base change is **not** a wall).
- ✅ **Module decomposition (I-2) COMPLETE** (2026-06-18, resume⁵): `IdempotentDirectSum`
  `isInternal_range_of_completeOrthogonalIdempotents` (complete orthogonal idempotent endos ⟹
  `M = ⊕ range`) + `CenterModuleDecomp` `isInternal_centerProj` (any `Representation k U W`
  decomposes via `centerProj φ ρ i = asAlgebraHom ρ (φ.symm (Pi.single i 1))`, the U-isotypic
  projections). Gives the `DirectSum.IsInternal A` the free-(†) engine consumes.
- ❌ **Main `wielandt_fixedPoint_frobenius` = the sole remaining sorry.** Next = carrier-level wiring
  of 3d.3c + (†) [I-2 isotypic + I-4 base change + I-3] + I-5; a DESIGN phase (see resume⁵ "NEXT").

## 2026-06-17 (resume³) — I-1 step (2) COMPLETE; step (3)/(4) plan

**I-1 build-order step (2) DONE** (`CenterClassSumBasis.lean`, lane-f, sorry-free + axiom-clean):
- `centerBasis : Basis (ConjClasses G) k ↥(Subalgebra.center k (MonoidAlgebra k G))` — the
  **class-sum basis over an arbitrary field** (`bbc3519c`). Helpers: `center_apply_conj`
  (central ⇒ class-constant coeffs, via `single_mul_apply`/`mul_single_apply`),
  `center_apply_of_mk_eq`, `center_eq_sum_classSum` (span half), `classSumCenter`/`Basis.mk`.
- `domCongr_classSum : domCongr α (classSum C) = classSum (ConjClasses.map α C)` — the **σ-permutation
  of the basis** by a group automorphism `α : G ≃* G` (`c4f52a6c`). Coefficient proof + `if_congr`,
  `MonoidHom.map_isConj` for `α`/`α.symm`.

**Lean gotchas hit** (memory [[lean-basis-in-module-namespace]]): (a) `Basis` is `Module.Basis` →
need `open Module` (import was fine all along; the bare-`import Basis.Basic` exposes it only namespaced;
cost ~6 build iters). (b) MonoidAlgebra application `z y` needs the codomain `k` pinned or it can't
synth `DFunLike k[G] G ?` — use `(z y : k)` ascription or `Finsupp.ext_iff` (not `DFunLike.congr_fun`,
which leaves the codomain a metavar). (c) `Finsupp.finset_sum_apply` won't `rw` on a MonoidAlgebra
sum (def wrapper, no syntactic match) → use `map_sum (Finsupp.applyAddHom y) _ univ` via a `have` then `rw`.

### Remaining: step (3) idempotent basis [hard core] + step (4) wiring
**Step (3) — `Z(𝔽̄_p[U]) ≅ 𝔽̄_p^N` idempotent basis** (the one remaining hard core):
`U` is `p′`, `𝔽̄_p` alg-closed ⇒ `𝔽̄_p[U]` split semisimple ⇒ `Z` split commutative semisimple ⇒
product of `𝔽̄_p`. mathlib API to use: `MonoidAlgebra` Maschke / `IsSemisimpleRing`,
`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` (Wedderburn-Artin: `𝔽̄_p[U] ≅ ∏ Mat_{n_i}`),
center of `Mat_n k = k·1` ⇒ `Z ≅ ∏ 𝔽̄_p` (N = #simples = #matrix blocks). The idempotent basis =
the standard basis of `∏ 𝔽̄_p` pulled back; `σ_e` permutes the factors = permutes simples. **Investigate
the exact `Mat`-center + `Pi`-algebra API before committing** (new infra, multi-session).

**Step (4) — cornerstone wiring** (shared by both bases): parametrise by a `MonoidHom ψ : G' →* MulAut G`
(`G'` arbitrary; instantiate `G' = ⟨e⟩` / the cyclic image for the Brauer count). Then:
- `MulAction G' (ConjClasses G)` via `g • C := ConjClasses.map (ψ g) C` (= `MulAction.compHom` of the
  `MulAut G`-action along `ψ`; the `MulAut G`-action on `ConjClasses G` is `ConjClasses.map`, needs
  `one_smul`/`mul_smul` = `ConjClasses.map` functoriality).
- `Representation k G' ↥center` = `domCongrAut k k` (a `MulAut G →* (k[G] ≃ₐ[k] k[G])`) **restricted to
  the centre** (an algebra auto preserves `Subalgebra.center`) precomposed with `ψ`.
- compatibility `ρ g (centerBasis C) = centerBasis (g • C)` = `domCongr_classSum` lifted to the subtype.
- apply `finrank_invariants_eq_card_orbits` **twice with the same `ρ`** (basis 1 = `centerBasis`/classes,
  basis 2 = idempotents/simples): `finrank k ↥(invariants ρ)` is intrinsic ⇒
  `#(G'-orbits on classes) = #(G'-orbits on simples)`.
Then the counting bridge (coprime-FPF free-on-nontrivial-classes via repo Glauberman + orbit-size
counting) ⇒ free `E`-action on nontrivial simples ⇒ feed I-3 ⇒ (†). See resume² for the bridge math.

**Step (4) class-sum side — DONE except the final line** (`CenterOrbitCount.lean`, commit `cab132a7`,
sorry-free + axiom-clean): I built it directly for `G' = MulAut G` (no `ψ` yet — instantiate to a
cyclic subgroup when wiring the Brauer count). Landed: `ConjClasses.map_id`/`map_comp`,
`instance MulAction (MulAut G) (ConjClasses G)` (`rfl` laws), `AlgEquiv.map_mem_center` (algebra autos
preserve the centre), `centerEnd`/`centerRep` (the representation, `show`-based structure-field
proofs), and the keystone **`centerRep_apply_centerBasis : centerRep α (centerBasis C) = centerBasis
(α • C)`** (= the cornerstone's `hρ`, via `domCongr_classSum`).
✅ **Capstone DONE** (`faeb1bc8`): `finrank_centerRep_invariants_eq_card_orbits :
finrank k ↥(invariants centerRep') = Nat.card (orbitRel.Quotient (MulAut G) (ConjClasses G))`.
The blocker was a **`Module k`-instance diamond** on `↥(Subalgebra.center k (MonoidAlgebra k G))`:
the instance baked into `centerRep` got defeq-checked against a re-derived one, exploding `isDefEq`
past 1M heartbeats (diagnosed via statement-only `… := by sorry` timeouts; bare `finrank k ↥center`
is fine, only `invariants centerRep` explodes). **Fix = carrier synonym** `CenterCarrier k G :=
↥(Subalgebra.center k (MonoidAlgebra k G))` with one pinned `Module k`-instance (`inferInstanceAs`);
`centerRep'`/`centerBasis'` retype through it definitionally and the cornerstone applies in ms.
Reusable technique: [[lean-type-synonym-fixes-instance-diamond]]. **⟹ the same synonym de-risks the
idempotent-side cornerstone application (step 3).**

### Step (3) — idempotent basis: crux DONE, Wedderburn transport remains
**σ-permutation crux ✅** (`PiAlgebraAut.lean`, commit `afa21d09`, self-contained + upstreamable):
`algEquiv_permutes_single : (ψ : (ι → k) ≃ₐ[k] (ι → k)) → ∃ π : Equiv.Perm ι,
∀ i, ψ (Pi.single i 1) = Pi.single (π i) 1`.  ⚠ The char-`p` pitfall: the column sum `∑ᵢ εᵢ j = 1`
does NOT force a unique nonzero entry (in char `p`, `p+1` ones also sum to `1`).  **Orthogonality**
(`εᵢ * εᵢ' = 0`) is what gives at-most-one nonzero per coordinate; supports are then pairwise
disjoint, cover `ι` (family sums to `1`), and `|ι|` nonempty disjoint covering sets are singletons
(`Finset.card` double-count).  This is the `hρ`-on-simples ingredient.

**Step (3) Wedderburn center transport ✅ DONE** (`CenterSplitting.lean`, commits `edba3d51` →
`3584c746`): `exists_center_algEquiv_pi : ∃ N, Nonempty (Z(k[U]) ≃ₐ[k] (Fin N → k))`.  Three reusable
links — `AlgEquiv.centerCongr` (`Z A ≅ Z B`), `centerPiEquiv` (`Z(∏ C) ≅ ∏ Z C`, via the
`mem_center_pi` characterisation), `matrixCenterEquiv` (`Z(Matₙ k) ≅ k`, via
`subalgebraCenter_eq_scalarAlgHom_map` + `scalar` injective) — composed with
`exists_algEquiv_pi_matrix_of_isAlgClosed` (`k[U] ≅ ∏ Matᵢ`, instances resolve under
`[IsAlgClosed k] [Finite G] [NeZero (Nat.card G : k)]`) and `piCongrRight`.

**Remaining step (3) = idempotent basis + cornerstone (simples side):** obtain `φ : Z ≅ (Fin N → k)`
from `exists_center_algEquiv_pi`; basis `b i := φ.symm (Pi.single i 1)`; the `σ`-permutation is
`algEquiv_permutes_single` applied to `φ.trans (σ.centerCongr-ish).trans φ.symm` on `(Fin N → k)`.
⚠ For the cornerstone we need a *group* action on `Fin N` (not just one `σ`): the map `σ ↦ π_σ` must
be a homomorphism.  Cleanest is to apply the cornerstone for a **single cyclic ⟨e⟩** (the Brauer
count is per-`e`): `dim ker(centerRep e − 1) = #(⟨π_e⟩-orbits on Fin N)`, with `⟨π_e⟩` the cyclic
group generated by the permutation `algEquiv_permutes_single` gives for `e`.  Through the
`CenterCarrier` synonym (de-risked) ⟹ `dim Z^{⟨e⟩} = #(orbits on simples)`.  Then equate with the
class-sum count (step 4) + the counting bridge ⟹ (†).

## 2026-06-17 (loop handoff) — step 3b in progress; HANDOFF for next session

A self-paced `/loop` ran 8 increments (all sorry-free + axiom-clean, full build green each commit,
3.0–3.7s). **Group-action coherence — the subtle part flagged above — is now RESOLVED** (`algAutPerm`
makes `σ ↦ π_σ` a genuine `MonoidHom`, so we get a real `MulAction` of *all* `MulAut G` on `Fin N`,
not just a single `⟨e⟩`).

**DONE this loop** (commits `afa21d09` → `f1527db4`):
- `PiAlgebraAut.algEquiv_permutes_single` (autos of `ι→k` permute the standard idempotents; the
  char-`p` crux) + **`algAutPerm : ((ι→k) ≃ₐ[k] (ι→k)) →* Equiv.Perm ι`** (`algAutPerm_apply_single`).
- `CenterSplitting.lean`: `AlgEquiv.centerCongr` / `centerPiEquiv` / `matrixCenterEquiv` /
  **`exists_center_algEquiv_pi : ∃ N, Nonempty (Z(k[G]) ≃ₐ[k] (Fin N → k))`** (step 3a, Wedderburn) /
  `AlgEquiv.centerCongrHom : Aut k[G] →* Aut Z`.
- `CenterSimplesOrbit.lean`: `centerRep_eq_centerCongr` + **`simplesAction φ : MulAut G →* Perm (Fin N)`**
  (`= algAutPerm ∘ autCongr φ ∘ centerCongrHom ∘ domCongrAut`) + **`centerRep_apply_symm_single`** =
  exactly the cornerstone's `hρ` on the simples side:
  `centerRep g (φ.symm (Pi.single i 1)) = φ.symm (Pi.single (simplesAction φ g i) 1)`.

**NEXT (resume here), in `CenterSimplesOrbit.lean`, given `φ` from `exists_center_algEquiv_pi`:**
1. `MulAction (MulAut G) (Fin N) := MulAction.compHom (Fin N) (simplesAction φ)` (Perm acts on its
   index; compose along the `simplesAction` hom). Likely a `letI`/`haveI` inside the final theorem.
2. idempotent basis `bIdem : Basis (Fin N) k ↥Z := (Pi.basisFun k (Fin N)).map φ.symm.toLinearEquiv`
   (`bIdem i = φ.symm (Pi.single i 1)` via `Pi.basisFun_apply`).
3. cornerstone (simples side): mirror `finrank_centerRep_invariants_eq_card_orbits` (the class-sum
   capstone in `CenterOrbitCount.lean:152`) — go through the **`CenterCarrier` synonym** (retype
   `bIdem`/`centerRep` to `CenterCarrier`, the instance-diamond fix [[lean-type-synonym-fixes-instance-diamond]]),
   feed `centerRep_apply_symm_single` as `hρ` ⟹
   `finrank k ↥(invariants centerRep') = Nat.card (orbitRel.Quotient (MulAut G) (Fin N))`.
4. **equate the two capstones** (both `= finrank ↥(invariants centerRep')`) ⟹ the Brauer orbit
   equality `#(MulAut G-orbits on ConjClasses G) = #(MulAut G-orbits on Fin N)`. ← step 3 payoff.
5. step 3d counting bridge: specialise the acting group to `⟨e⟩` (a cyclic subgroup of `MulAut G` /
   the Frobenius element's action — `MulAction` restricts to a subgroup automatically); Glauberman
   free-on-nontrivial-classes (`coprime` FPF, repo `glauberman_fixed_points_conj`) ⟹
   `#orbits-classes = 1 + (Ncl−1)/d`; transfer via the Brauer equality + `Nsimples = Ncl` ⟹ free
   `E`-action on nontrivial simples ⟹ (†) ⟹ feed I-3 ⟹ `wielandt_fixedPoint_frobenius`.

⚠ The remaining `CoprimeAction.lean` sorry does NOT drop until the full (9.1) assembly (step 3d +
I-3 + I-4 + I-5 + the main-formula glue); step 3a/3b are reusable infra, sorry-count-neutral so far.
Loop cadence was 60s (no external gate). `bin/count-sorry` = 139.

## 2026-06-17 (resume⁴) — steps 1-4 DONE: the Brauer orbit equality landed

Completed the loop handoff's steps 1-4 in `CenterSimplesOrbit.lean` (`f26fd70c`, sorry-free,
`#print axioms` = {propext, Classical.choice, Quot.sound}):

- `idemBasis φ : Basis (Fin N) k (CenterCarrier k G)` = `(Pi.basisFun k (Fin N)).map
  φ.symm.toLinearEquiv` (the primitive-idempotent basis, retyped over `CenterCarrier`).
- `centerRep'_apply_idemBasis` = simples-side `hρ`: `centerRep' g (idemBasis φ i) =
  idemBasis φ (simplesAction φ g i)` (massage `idemBasis φ j = φ.symm (Pi.single j 1)` via
  `Basis.map_apply` + `Pi.basisFun_apply`, then `centerRep_apply_symm_single`).
- `finrank_centerRep_invariants_eq_card_orbits_simples` = cornerstone applied to `idemBasis`:
  `dim Z^{MulAut G} = #(MulAut G-orbits on Fin N)`. **Stated with `[MulAction (MulAut G) (Fin N)]`
  + `hact : ∀ g i, g • i = simplesAction φ g i` as decoupled hypotheses** (rather than a
  term-dependent instance keyed on `φ`): the caller supplies `MulAction.compHom (Fin N)
  (simplesAction φ)`, for which `hact` holds by `rfl` (`compHom_smul_def` + `Perm.smul_def`).
- `card_orbits_classes_eq_card_orbits_simples` = **the orbit-count Brauer equality**
  `#(orbits on ConjClasses G) = #(orbits on Fin N)` — both sides `= dim Z^{MulAut G}` (class-sum and
  idempotent bases), so they agree. No char-0 / Teichmüller.

**NEXT — step 3d (counting bridge), toward (†):**
1. ✅ **DONE (3d.1, `78f8c86f`)** — orbit equality for an arbitrary acting group via a hom
   `ψ : Γ →* MulAut G`: `centerRepComp ψ = centerRep'.comp ψ : Representation k Γ (CenterCarrier k G)`
   (a `Representation` IS a `MonoidHom` to `Module.End`, so `MonoidHom.comp` typechecks; ascription
   pins the carrier), cornerstone twice ⟹ `card_orbits_classes_eq_card_orbits_simples_comp :
   #(Γ-orbits on classes) = #(Γ-orbits on simples)`. For `Γ = ↥(Subgroup.zpowers e)`,
   `ψ = Subgroup.subtype`, `compHom`-action on `Fin N`, the agreement hyps `hcl`/`hsi` hold by `rfl`.
2. ✅ **DONE (3d.2, `dccd7dd3`)** — "coprime-FPF automorphism fixes only the trivial class":
   `CenterOrbitFree.map_eq_self_imp_eq_trivial_of_fpf` — for `β : MulAut G` with `⟨β⟩` coprime to
   `|G|` and FPF (`β x = x → x = 1`), a `β`-fixed class `C` (`β • C = C`) is `mk 1`. Built via
   `glauberman_fixed_point_exists` (Isaacs 3.24(a)) on `Ω = {y // mk y = C}` (transitive `G`-conj
   set; `⟨β⟩` acts via `β`, compatible); the `β`-fixed element is in `Fix(β) = {1}`. `⟨β⟩` solvable
   via `isSolvable_of_comm` + `mul_comm'` (zpowers `IsMulCommutative`). sorry-free, axiom-clean.
3. **(3d.3) transfer to simples** — **abstract backbone COMPLETE** (3d.1/3d.2/3d.3a/forward-count
   all sorry-free + axiom-clean); remaining = the rep-theory `i₀` identification + concrete wiring.
   - ✅ **forward-count DONE (`9b64a344`)** — `FreeActionOrbitCount.card_orbits_eq_of_free_off_unique_fixed`
     (unique fixed point + free elsewhere ⟹ `#orbits = 1 + (n−1)/d`; 3d.3a's converse, defect sum via
     `Finset.sum_eq_single`). The class side feeds this (Γ=E, x₀=trivial class, free-off-trivial by 3d.2).
   - ✅ **(3d.3a) DONE (`9ec8db73`)** — `FreeActionOrbitCount.orbit_trivial_or_free_of_card_orbits`:
     finite `Γ` (order `d > 1`) on finite nonempty `S` with `#orbits = 1 + (n−1)/d` and `d ∣ n−1` ⟹
     **every orbit size `1` or `d`, at most one fixed point**. The divisor argument went through as
     worked out (no primality): `∑ᵢ (d − sᵢ) = d − 1`, each proper-divisor defect `≥ d/2` (via
     `2sᵢ ≤ d`), so `#{proper}·d ≤ 2(d−1) < 2d ⟹ ≤ 1` proper orbit, of size `1`. Helpers
     `card_orbit_dvd_card_group` (orbit-stabiliser `index_dvd_card`), `two_mul_le_of_dvd_of_lt`,
     `orbit_eq_singleton_of_mem_fixedPoints`. sorry-free, axiom-clean.
   - **(3d.3b) the trivial simple is `MulAut G`-fixed** — **crux infra ✅ DONE (`cf2c9387`)**:
     `PiAlgebraAut.algHom_pi_eq_eval` (an algebra hom `(ι→k)→ₐ[k] k` is a coordinate evaluation `i₀`,
     via the orthogonal-idempotent technique). **Remaining assembly**: the trivial central character is
     the augmentation `aug : Z(k[U]) →ₐ[k] k`; apply `algHom_pi_eq_eval` to `aug ∘ φ.symm` ⟹
     `∃ i₀, ∀ z, aug z = φ z i₀`. `aug` is automorphism-invariant (`aug (centerRep α z) = aug z`, as `α`
     permutes `G`), and `φ ∘ centerRep α` permutes coordinates by `simplesAction φ α`
     (`centerRep_apply_symm_single`), so `simplesAction φ α i₀ = i₀` — `i₀` is the fixed simple.
     ⚑ This **supersedes** the earlier "symmetriser idempotent is primitive" route (no block theory).
     [OLD route, for reference:] The trivial central
     idempotent `t = (1/|U|) ∑_{g} single g 1 ∈ Z(k[U])` is `MulAut`-fixed (`α(∑ g) = ∑ g`) and is a
     primitive idempotent, so `t = idemBasis φ i₀` for some `i₀`; `centerRep_apply_symm_single` then
     forces `simplesAction φ α i₀ = i₀`, so `i₀ ∈ fixedPoints`.
   - **(3d.3c) combine:** Brauer equality (3d.1, `Γ = E` via the orbit hom) + `Nsimples = Ncl`
     (equal `finrank Z`) + "`E` free on nontrivial classes" (3d.2 per `e ∈ E#`) gives
     `#orbits-classes = 1 + (Ncl−1)/|E|` [needs a **forward-count** lemma: an action with one fixed
     point and free elsewhere has `#orbits = 1 + (n−1)/d` — the converse of 3d.3a, also via the
     orbit partition]; then `#orbits-simples = 1 + (Ncl−1)/|E|`; (3d.3a) ⟹ exactly one fixed simple +
     rest free; (3d.3b) ⟹ that fixed simple is the trivial one ⟹ **`E` free on the nontrivial
     simples**. ⚠ 3d.3c also needs `1 < |E|` (E nontrivial — holds: Frobenius complement) and the
     wiring of the abstract `Γ`-action to the concrete `simplesAction φ`/`Fin N` (compHom + `rfl`
     agreement, as set up in 3d.1).
   Then (†): I-2 isotypic decomposition of `W` (`W^U = 0` ⟹ only nontrivial components) + I-4 base
   change `𝔽_p → 𝔽̄_p` + per-orbit I-3 (`finrank_eq_card_mul_finrank_invariants`) ⟹
   `dim W = |E|·dim W^E`.

`Nsimples = Ncl`: `idemBasis` is indexed by `Fin N` and `centerBasis` by `ConjClasses G`, both bases
of the same `Z(k[G])`, so `N = #(ConjClasses G)` (equal `finrank`) — the `dim`-equality, not a
separate fact.

## 2026-06-18 (resume⁵) — I-1 abstract backbone COMPLETE (3d.3b + 3d.3c landed)

Both remaining step-3d pieces landed (sorry-free, axiom-clean = {propext, Classical.choice,
Quot.sound}), so the **Teichmüller-free orbit-count Brauer lemma is complete at the abstract level**
(the original "char-0 lifting wall" is dissolved — never needed):

- **3d.3b assembly** (`1ba00224`, `CenterSimplesOrbit.exists_fixed_simple`): the trivial simple `i₀`
  is `MulAut G`-fixed. Built the augmentation `aug : Z(k[G]) →ₐ[k] k` = `MonoidAlgebra.lift 1`
  restricted to the centre (`aug`/`aug_apply`), proved `centerRep`-invariance `aug_centerRep` (via
  `lift_one_comp_domCongrAut`: `lift 1 ∘ domCongrAut α = lift 1` by `algHom_ext` on `single`), applied
  `PiAlgebraAut.algHom_pi_eq_eval` to `aug ∘ φ.symm` to name `i₀`, and `centerRep_apply_symm_single`
  forces `simplesAction φ α i₀ = i₀`. **No block theory.**
- **N=Ncl** (`93a83924`, `CenterSimplesOrbit.card_simples_eq_card_classes`): `N = #(ConjClasses G)`
  via `Module.finrank_eq_card_basis` on `idemBasis φ`/`centerBasis'`. Needs `include φ in` (statement
  doesn't mention `φ`/`k`).
- **divisibility** (`93a83924`, `FreeActionOrbitCount.dvd_card_sub_one_of_free_off_unique_fixed`):
  free-off-unique-fixed ⟹ `|Γ| ∣ |S|−1` (split off `⟦x₀⟧`: `|S| = 1 + (#orbits−1)·|Γ|`). Feeds 3d.3a.
- **3d.3c combine** (`93a83924`, `CenterOrbitFree.gamma_free_off_trivial_simple`): finite `Γ` via
  `ψ : Γ →* MulAut G` (each nonid `ψ γ` FPF + `⟨ψ γ⟩` coprime) ⟹ on `Fin N`, `i₀` unique fixed +
  free off it. Class side free-off-`mk 1` (3d.2 ×2: uniqueness + trivial stabilisers via
  `orbitEquivQuotientStabilizer` + `quotientBot`); `card_orbits_eq_of_free_off_unique_fixed` +
  divisibility carry to simples by Brauer (3d.1) + N=Ncl; 3d.3a ⟹ free-off-single-fixed; 3d.3b names
  it `i₀`. Caller supplies `Γ`-actions by `compHom` (agreement `hcl`/`hsi` by `rfl`).

**NEXT — carrier-level (abstract engines + I-2 module decomposition now DONE):**
0. **★ THE next concrete piece — the E-conjugation → `simplesAction` module bridge**: for `e ∈ E`
   acting on `W` (via `ρ_L`, `L = U⋊E`), show `ρ_L(e)` maps `range (centerProj φ ρ_U i)` onto
   `range (centerProj φ ρ_U (simplesAction φ (conjAut e) i))`. Ingredients: (a) semilinear
   compatibility `ρ_L(e) ∘ asAlgebraHom ρ_U a = asAlgebraHom ρ_U (domCongrAut (conjAut e) a) ∘ ρ_L(e)`
   (from `ρ(e)ρ(u)ρ(e)⁻¹ = ρ(eue⁻¹)`, `U ◁ L`); (b) `domCongrAut (conjAut e) ε_i = ε_{σ e i}` (=
   `centerRep_apply_symm_single`, center level). ⟹ the `A i := range (centerProj i)` are an
   `E`-permuted family with permutation `simplesAction φ ∘ conjAut`, matching the free-(†) engine's
   `hperm`. Est. ~100-150 lines; the genuinely-coupled crux.
1. **Wire 3d.3c to the real carrier**: in `CoprimeAction`, kernel `U` + complement `E` of Frobenius
   `L = U ⋊ E`; `ψ = E → MulAut U` (conjugation, each nonid FPF by Frobenius + coprime); splitting
   `φ : Z(𝔽̄_p[U]) ≃ₐ (Fin N → 𝔽̄_p)` from `exists_center_algEquiv_pi` (needs `IsAlgClosed`,
   `char ∤ |U|`).
2. **(†)** `W^U = 0 ⟹ dim W = |E|·dim W^E`: **the abstract engine
   `finrank_eq_card_mul_finrank_invariants_of_free` is DONE** (resume⁵). Remaining = *wire the module*:
   take `A i := (idemBasis φ i) · W` (idempotent projections = I-2 isotypic comps, internal since the
   `idemBasis` are a complete orthogonal idempotent family of `Z(𝔽̄_p[U])`); show `E` permutes them by
   `simplesAction φ` (conjugation permutes central idempotents — the bridge to 3d.3c); `W^U = 0 ⟹`
   trivial comp `A i₀ = ⊥`, so restrict to `ι = {i ≠ i₀}` where `E` is free (3d.3c) ⟹ apply the engine.
3. **I-4 base change** `𝔽_p → 𝔽̄_p` (chief factors live over `𝔽_p`). **NOT a wall**: `dim` is preserved
   by `Module.finrank_baseChange`; invariants commute with base change via the coprime averaging
   idempotent (`𝔽̄_p` free over `𝔽_p`). Build the `(𝔽̄_p ⊗ W)^E ≅ 𝔽̄_p ⊗ Wᴱ` finrank identity.
4. **(I-5)** chief-series multiplicativity `|C_H(X)| = ∏ |C_{V_i}(X)|` (keystone Cor 3.28 exists).
5. assembly → `wielandt_fixedPoint_frobenius` (`CoprimeAction.lean` sole sorry).

## Decision (2026-06-17, user): NO axioms — build everything bottom-up

The full (9.1) splits into a **qualitative** half (corollary (i)) and a **counting**
half (full formula + corollary (ii)):

- **Corollary (i)** `C_H(E)=1 ⇒ U central`: Brauer-free, via the repo's sorry-free
  module-level Wielandt (BG Lemma 3.3) + chief series.  No char-0 input.
- **Full formula + corollary (ii)**: need the elementary-abelian **counting** (†),
  which reduces to "`E` acts freely on the nontrivial irreducible `𝔽_p[U]`-modules".
  ⚠ This is a **modular** Brauer permutation lemma (over `𝔽̄_p`, for the `p′`-group `U`);
  the repo's `BrauerPermutation*.lean` is **ℂ-character only** and does not bridge to
  `𝔽_p`-modules.  A char-0 bridge (Brauer characters / `p′`-lifting, or a `Z(𝔽̄_p[U])`
  trace-lift) is genuinely required and is **absent from repo + mathlib**.

**User directive (2026-06-17): build this missing infrastructure bottom-up, no axioms.**
FT-path confirmed ((9.1) → Pf §11→§12/13→§14→§15→§16 → S16.Hypothesis → `feitThompson`);
no lane interference (F owns `CoprimeAction` + new `GroupTheory/RepresentationTheory/*`;
lanes b/g/h touch none of these).

### Existing foundations to reuse (cite, read-only)

- `OddOrder/BG/Ch1_Preliminary/S03b_Lemma33.lean` (sorry-free): module-level Wielandt
  (BG Lemma 3.3) via `groupSumMap ρ H = ∑_{h∈H} ρ h`; gives
  `kernel_acts_trivially_of_centralizer_eq_bot` (C_V(R)=0 ⇒ kernel trivial) — for cor (i).
- `OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean` — operator Maschke (projection).
- `Representation.invariants` + `averageMap`/`isProj_averageMap` (mathlib) — used in
  `WielandtCounting.lean` for the coprime decomposition `V = V^G ⊕ [V,G]`.
- `IsFrobeniusGroup` + `SubgroupPartition`/`frobeniusGroup h`: set-partition
  `L = U ⊔ ⨆_{u∈U} (E^u)#`, parts pairwise-TI, card `|U|+1`.
- ⚠ repo `BrauerPermutation*.lean` is **ℂ only** — NOT directly usable for (†); the
  modular analogue must be built (the `Z(𝔽̄_p[U])` slick proof needs a char-0 trace lift).

## Route B (the planned proof)

`L = UE` Frobenius (kernel `U`, complement `E`), coprime action on finite solvable `H`.
Goal: `|C_H(UE)|^|E| · |H| = |C_H(E)|^|E| · |C_H(U)|`.

1. **Solvable → elementary-abelian reduction.** Take an `L`-invariant series of `H` with
   el-ab `p`-group factors `V_i` (solvable + coprime). For coprime action,
   `C_{H/N}(X) = C_H(X)N/N`, hence `|C_H(X)| = ∏_i |C_{V_i}(X)|` for every `X ≤ L`.
   The product formula multiplies over factors, so (9.1) reduces to the el-ab identity
   on each `V_i`.
2. **El-ab identity (⋆).** For `V` an `𝔽_p[L]`-module (`p ∤ |L|`):
   `|E|·dim V^L + dim V = |E|·dim V^E + dim V^U`  (this is `log_p` of (9.1) on `V`).
   Proof: coprime split `V = V^U ⊕ [V,U]` (both `L`-invariant since `U ◁ L`). With
   `V^{UE} = (V^U)^E` and `[V,U]^U = 0`, (⋆) collapses to the kernel-FPF fact (†) on
   `W := [V,U]`.
3. **Kernel-FPF dim fact (†).** `W` an `𝔽̄_p[L]`-module, `W^U = 0` (`U` acts FPF). Then
   `dim W = |E|·dim W^E`.
   Proof: Maschke-decompose `W` into nontrivial `U`-isotypic components; `E` (Frobenius
   complement, every non-id element FPF on `U`) acts **freely** on the nontrivial
   irreducible `U`-modules — by a **modular** Brauer permutation lemma the only `H'`-fixed
   irreducible (for `1 ≠ H' ≤ E`) is trivial. Hence `E`-orbits on components have size
   `|E|`, and `W^E` picks one representative dimension per orbit ⇒ `dim W = |E|·dim W^E`.
   ⚠ **The modular Brauer permutation lemma is the new infra to build** (§ below).
   Work over `𝔽̄_p` (alg. closed, split); descend to `𝔽_p` via base change
   (`dim_{𝔽_p} V^X = dim_{𝔽̄_p} (V ⊗ 𝔽̄_p)^X`).

### New infrastructure (bottom-up, no axioms) — sub-pieces / sub-issues

- **(I-1) modular Brauer permutation lemma** over `𝔽̄_p` for a `p′`-group `U`:
  for an automorphism action, `#(fixed irreducible 𝔽̄_p[U]-modules) = #(fixed classes)`.
  Slick route: `Z(𝔽̄_p[U])` has two bases (class sums ↔ classes; primitive idempotents ↔
  simples), both permuted by the automorphism; equate the **char-0 trace lift** of the
  permutation operator.  ⇒ needs a char-0 trace of a permutation of a `𝔽̄_p`-basis
  (integer #fixed, not mod p) — the genuine new content.
- **(I-2) isotypic decomposition** of a semisimple `𝔽̄_p[U]`-module (mathlib
  `IsSemisimpleModule` + `Maschke`; isotypic components may need building).
- **(I-3) regular-orbit fixed-space count**: `E` permutes summands `{W_S}` regularly ⇒
  `dim ⊕_S W_S = |E|·dim (⊕_S W_S)^E` (abstract, Brauer-free).
- **(I-4) base change** `𝔽_p → 𝔽̄_p` for fixed-point dimensions (flat).
- **(I-5) chief-series coprime machinery**: `C_{H/N}(X)=C_H(X)N/N`, `L`-invariant el-ab
  series of solvable `H`, multiplicativity `|C_H(X)|=∏|C_{V_i}(X)|`.

Build order (least → most dependent): I-3 (abstract) → step 2 (⋆, Brauer-free) →
cor (i) via BG 3.3 + I-5 → I-2 → I-1 → (†) → I-4 → assembly.

## 2026-06-17 (loop) — I-1 confirmed as the char-0 wall; mathlib status

Step 2 (⋆ `finrank_elab_identity`) DONE. Drilling into I-1 (the (†) core) confirmed it
genuinely needs **char-0 / Brauer-character** infrastructure — no char-p bypass:

- (†) ⟸ "**E acts freely on the nontrivial 𝔽̄_p[U]-simple modules**" ⟸ Brauer permutation
  lemma in **FIXED-POINT form** over 𝔽̄_p: `#(e-fixed simples) = #(e-fixed classes)` for `e∈E`.
- The char-p trace of the conjugation permutation on `Z(𝔽̄_p[U])` gives `#fixed ≡ #fixed (mod p)`
  only. `dim ker(σ_e − 1)` gives **#orbits**, not #fixed-points. So the linear-algebra /
  cycle-type route yields #orbits, not the #fixed-points the free-action argument needs.
- Genuine fixed-point equality needs the **char-0 trace** ⇒ Brauer characters / the `p′`
  decomposition-map bijection (`𝔽̄_p`-simples ↔ ℂ-irreducibles, equivariant). This is the
  classical content and is **absent from mathlib**.
- **mathlib DOES have** (helps I-2/I-3, Brauer-free): `RingTheory/SimpleModule/Isotypic.lean`
  (`isotypicComponent`, `IsIsotypic`, `linearEquiv_fun`), `SimpleModule/WedderburnArtin.lean`,
  `finrank_directSum`. **mathlib does NOT have**: Brauer characters, `p′` root-of-unity lift
  `𝔽̄_p→ℂ`, decomposition map.
- ⇒ Building I-1 bottom-up = building (a chunk of) **Brauer-character theory for `p′`-groups**
  from scratch (Teichmüller-style lift of `p′`-roots of unity, Brauer char as char-0 class
  function, the permutation lemma). Estimate **several sessions** on its own.

This is the loop's designated stop-point ("I-1 requires full Brauer-character theory").
Surfaced to user 2026-06-17 for a scope decision.

## 2026-06-17 (resume²) — ⚡ I-1 REDESIGN: #orbits suffices, NO Teichmüller lift

**The "char-0 wall" above is AVOIDABLE.** The earlier note assumed (†)'s free action needs
`#(e-fixed simples) = #(e-fixed classes)` (a #fixed-points equality ⟹ Teichmüller). But **#orbits is
enough** — and `#orbits` is exactly what the char-`p` linear algebra gives for free. User chose
"attack I-1" (2026-06-17); this is the route.

**Key fact (any field, any permutation basis):** for a linear `σ` that permutes a basis `B`,
`dim ker(σ − 1) = #(⟨σ⟩-orbits on B)` (invariants = orbit sums). So on `Z := Z(𝔽̄_p[U])`, with the
algebra automorphism `σ_e` induced by `e`:
- **class-sum basis** (`σ_e` permutes class sums by `e` on classes) ⟹ `dim ker(σ_e−1) = #(⟨e⟩-orbits
  on classes)`.
- **idempotent/coordinate basis** `Z ≅ 𝔽̄_p^{#simples}` (`U` `p′` ⟹ `𝔽̄_p[U]` split semisimple ⟹ `Z`
  split commutative semisimple ⟹ product of `𝔽̄_p`; `σ_e` permutes the factors = simples) ⟹
  `dim ker(σ_e−1) = #(⟨e⟩-orbits on simples)`.
- `dim ker` is basis-independent ⟹ **`#(⟨e⟩-orbits on classes) = #(⟨e⟩-orbits on simples)`** over
  `𝔽̄_p`. **No char-0, no Teichmüller.**

**Bridge #orbits ⟹ free action (the step the old note missed):** let `d = ord e`, `N = #classes =
#simples`.
- Every nonidentity power `e^j` (`1≤j<d`) is FPF on `U` (Frobenius complement) ⟹ fixes only the
  trivial class (coprime FPF: an `e^j`-fixed class has an `e^j`-fixed element = `1`; cf. repo
  `glauberman_fixed_points_conj`) ⟹ **`⟨e⟩` acts freely on the `N−1` nontrivial classes** ⟹
  `#(⟨e⟩-orbits on classes) = 1 + (N−1)/d`.
- Transfer: `#(⟨e⟩-orbits on simples) = 1 + (N−1)/d` too. The trivial simple is a fixed point (1
  orbit); the `N−1` nontrivial simples split into `(N−1)/d` orbits, each of size dividing `d`,
  summing to `N−1`. Max possible sum `= d·(N−1)/d = N−1`, achieved ⟺ **every orbit has size `d`** ⟹
  `⟨e⟩` acts freely on nontrivial simples ⟹ `e` fixes no nontrivial simple.
- ∀ `e ∈ E#` ⟹ `E` acts freely on nontrivial simples ⟹ (†) via I-3 (orbits of size `|E|`).

**Revised I-1 plan (Teichmüller-free), build order:**
1. abstract `dim ker(σ−1) = #orbits` for a basis-permuting linear map (pure linear algebra).
2. `Z(𝔽̄_p[U])` class-sum basis + `σ_e` permutes it (mathlib: center of `MonoidAlgebra`, class sums).
3. `𝔽̄_p[U]` (`p′`, `𝔽̄_p` alg-closed) split semisimple ⟹ `Z ≅ 𝔽̄_p^{simples}`, idempotent basis,
   `σ_e` permutes factors (mathlib `IsSemisimpleRing`/`WedderburnArtin` + comm-ss-over-alg-closed
   splitting).
4. equate #orbits; coprime-FPF free-on-nontrivial-classes (repo Glauberman) + the counting bridge.
5. ⟹ free `E`-action on nontrivial simples ⟹ feed I-3 ⟹ (†).
The hard core is now **(2)+(3) the two bases of `Z`** (standard finite-dim algebra, char-`p` OK), NOT
Brauer-character theory. Still multi-session but materially smaller. ⇒ supersedes the "char-0 wall"
verdict for the (†) route.

## Effort (no-axiom, revised 2026-06-17)

Larger than the earlier (over-optimistic) ~3–5 estimate, because (I-1) the **modular
Brauer permutation lemma** (char-0 trace-lift of a `𝔽̄_p`-basis permutation) is genuine
new infrastructure, not a reuse of the repo's ℂ lemma:
- I-3 regular-orbit count (abstract): ~0.5–1
- step 2 (⋆) Brauer-free: ~0.5–1
- cor (i) via BG 3.3 + I-5 chief-series: ~1–2
- I-2 isotypic + I-1 modular Brauer + (†): ~2–4 (the hard core)
- I-4 base change + assembly: ~1
**Estimate ~6–9 sessions.** Each leaf is sorry-free and committable independently
(robust if F is pivoted back to §16 when H lands `typeP_duality`).  If I-1 balloons
(e.g. forces full `p`-adic lifting), re-flag to user.

## 2026-06-17 (resume) — source proof confirmed + reusable-infra map + cor (i) plan

**I-3 COMPLETE** (`WielandtCounting.lean`, commit `b95fcc6b`): reverse half
`finrank_invariants_le_finrank_A1` + capstone `finrank_eq_card_mul_finrank_invariants`
(`dim V = |G|·dim V^G` for a regular `G`-orbit). Abstract Brauer-free; feeds (†) per `E`-orbit.

**Source proof read** (`04.11_…mmd` (9.1)): Peterfalvi cites **Wielandt ([HB] XI.12.4)** as a black
box and applies it to the Frobenius group-ring identity `U·E + |U|·1 = ∑_{u∈U} E^u + U` (= `L + |U|·1
= ∑_u E^u + U` since `underline U · underline E = underline L`), giving
`|C_H(UE)|^{|UE|}|H|^{|U|} = (∏_u |C_H(E^u)|^{|E|})|C_H(U)|^{|U|}`; `|U|`-th root + `E^u` conjugate ⟹
(9.1). **So the crux IS Wielandt's theorem** (not in mathlib).

**Route B reaffirmed over a "cleaner" Brauer-character route.** The uniform route
"`dim V^S = (1/|S|)∑_{s∈S} β_V(s)` (β = char-0 Brauer char) + group-ring linearity" needs the FULL
Brauer character ring. Route B's slice = the **permutation fixed-point lemma** (`#e-fixed simples =
#e-fixed classes`, integer form via Teichmüller) — a SMALLER Brauer slice. ⟹ keep Route B; I-3 + (⋆)
`finrank_elab_identity` stay on-path.

### 🎯 Reusable infrastructure FOUND (the I-5 chief-series machinery already exists)
- **keystone** `OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient` (+ `_of_coprime_normal`),
  `ForwardFromCh03.lean:794/808` = **Isaacs Cor 3.28** in EXACTLY the `φ : A →* MulAut G` form:
  coprime + (A or G solvable) + `IsAInvariant φ N` + A-fixed coset `∀a, φ a g ∈ gN` ⟹ ∃ fixed rep
  `c` (`∀a, φ a c = c`) with `c ∈ gN`. This is "`C_{G/N}(A) = image C_G(A)`" — the I-5 hard direction.
- **BG 3.3** `S03b.kernel_acts_trivially_of_centralizer_eq_bot`: Frobenius `G=KR` + `C_V(R)=0` +
  `(|K|:F)≠0` ⟹ `K` trivial on `V`. (qualitative module Wielandt.)
- **el-ab bridge** `GroupTheory.ElementaryAbelianRepresentation`: `MulDistribMulAction G M` (M el-ab
  p) ⟹ `Representation (ZMod p) G (Additive M)` via `ofDistribMulAction` (+ the `SMulCommClass`
  instance). `φ : L →* MulAut H` gives `MulDistribMulAction L H` by `compHom`.
- **chief series** `GroupTheory.ChiefFactor`: `chiefSeriesInside`, `IsChiefFactor`,
  `chiefFactorCentralizer`, `chiefFactor_isElementaryAbelian` (S03c).
- **stability (Frattini case)** `Ch04.aFixed_quotient_frattini` = Isaacs Cor 3.29: A trivial on
  `G/Φ(G)` ⟹ A trivial on `G`. (Pattern for the general stability step.)
- BG 3.7 internal machinery (`S03c_Thm37.lean`) is all tied to `chiefFactorConjAction` (internal
  conjugation) — NOT directly reusable for the external `φ`, but the same induction shape.

### cor (i) assembly plan (Brauer-free, achievable NOW)
`C_H(E)=1 ⟹ U trivial on H`, strong induction on `Nat.card H`:
1. `H=1` trivial; else take **N = minimal `φ(L)`-invariant normal ≤ H** (el-ab, exists in nontrivial
   solvable `φ(L)`-group). [new piece — minimal invariant normal]
2. **N**: `C_N(E) ≤ C_H(E)=1` ⟹ `C_N(E)=0`; el-ab bridge + **BG 3.3** ⟹ `U` trivial on `N`.
3. **H/N**: keystone (`coprime_fixedPoints_quotient`) ⟹ `C_{H/N}(E)=1`; descend `φ` to `φ̄ : L →*
   MulAut(H/N)` (needs `IsAInvariant φ N`); induction ⟹ `U` trivial on `H/N`.
4. **stability (el-ab N)**: `α := φ u` fixes `N` pointwise and `h⁻¹·α h ∈ N` ∀h ⟹ `α^k h = h·(h⁻¹ α
   h)^k` (clean computation, `α|_N=id` kills the cross terms) ⟹ `α^p = id` (el-ab N exponent p);
   `α^{|u|}=id`, `gcd(p,|u|)=1` ⟹ `α=id`. [new piece — self-contained helper]
New pieces = (1) minimal invariant normal + (4) el-ab stability + the `φ`-descent wiring. Everything
else cites the found infra. ⟹ makes `wielandt_fixedPoint_trivial_E_fixed` unconditional (de-gates it
from the sorried main formula). Does NOT drop sorry count (main formula `wielandt_fixedPoint_frobenius`
still sorried, needs I-1 wall) but is genuine on-path progress (I-5 application validated).

## Not on the immediate critical path

(9.1) is consumed by (9.3) → §11, which is Lane-B character-API-gated and far downstream;
finishing (9.1) closes the local `CoprimeAction.lean` sorry but unblocks nothing now.

## 2026-06-21 (lane-h pickup) — (9.1) は |P|=p^q の deepest pole と判明、lane-h が完成を driving

ユーザーが lane-h を **§14 体構造 |P|=p^q** に向けた (lane-h POLE-2 frontier が cross-lane gate で
exhausted → 選択肢「§14 体構造に着手」を採択)。その honest path を辿ると **|P|=p^q ⟹ Pf (9.1) Wielandt**
に bottom-out する (チェーン全体の deepest pole):

```
Pf (13.2.b) |P|=p^q  ← (10.11)[II]+(11.7)[III] ← (9.3)|H|=|W₂|^q + (9.6) ← (9.1) Wielandt
```

- (13.2.b) `basic_structure.P_order`/`card_Q_eq` (S15, sorry) ← (10.11) `theorem88_caseB_prime_orders`
  は **primality のみ証明済**で |H|=p^q 部分は別 (S12) / (11.7) `H_elementaryAbelian` (S13, sorry)。
- (9.3) `typeII_III_IV_order_relations` (S11, sorry): Type II で C_H(U)=1 [(8.6.b)/(8.12.b)] +
  **|H|=|C_H(W₁)|^q [(9.1)]** = |W₂|^q。⟹ (9.1) cor (ii) (`wielandt_fixedPoint_trivial_U_fixed`) が core。

**∴ lane-h は本 design の (9.1) 完成を pickup** (lane-f は §16/§14 に pivot して parked; ファイルは
lane-f 現 frontier と disjoint, 衝突低)。issue 2014。**進め方** (CLAUDE.md「難所を回避しない」+ lane 領域):
1. **group-theoretic 層を先に** (lane-h strength, (†) と decouple):
   - el-ab card↔dim bridge `Fintype.card ↥(C_V(X)) = p^finrank invariants`
     (`Module.card_eq_pow_finrank`: `Fintype.card V = Fintype.card K ^ finrank K V`, K=ZMod p)。
   - **I-5 chief-series multiplicativity** `|C_H(X)| = ∏_i |C_{V_i}(X)|`
     (`ChiefFactor.chiefSeriesInside`/`_exists_eq_bot` + Isaacs Cor 3.28
     `coprime_fixedPoints_quotient`, telescoping over the L-invariant chief series)。
   - assembly skeleton: per-factor (⋆) `finrank_elab_identity` を p_i-power して掛け、群 (9.1) に。
     ⟹ `wielandt_fixedPoint_frobenius` を **(†)-per-chief-factor の named residual modulo** で証明。
2. **(†) module wiring** (resume⁵ NEXT items 0-3, lane-f coupled rep-theory) を最後に discharge
   (done engine 群を carrier に wire; lane-f 知見と要調整)。

⚠ resume⁵ NEXT (items 0-5) が依然ロードマップ; 上記 1 = items 4-5 を group 層から先取りして (†) を
clean に isolate する順序。実 sorry は assembly 完了まで不変 (`wielandt_fixedPoint_frobenius` 1 本)。

## 2026-06-21 (lane-h resume²) — chief-step fixed-point multiplicativity toolkit DONE

新 leaf `OddOrder/GroupTheory/CoprimeFixedPoints.lean` (sorry-free + axiom-clean, AxiomsCheck 5 本,
full build 3873 green)。assembly 帰納の群論的核を両側そろえた:

- **`card_fixedSubgroup_eq_mul`** (商側, chief step `1→N→H→H/N→1`): coprime+solvable 作用
  `φ:L→*MulAut H`, `X≤L`, L-不変正規 `N◁H` で `|C_H(X)| = |C_H(X)⊓N| · |C_{H/N}(X)|`。
  核 = reduction map `C_H(X)→*H/N` の image=`C_{H/N}(X)` (`map_fixedSubgroup_eq_fixedSubgroup_quotient`
  = Isaacs Cor 3.28 `OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient`), kernel=`C_H(X)⊓N`
  (Lagrange + Noether 第一同型)。`C_{H/N}(X)` の誘導商作用 = `IsAInvariant.quotientMulAutHom`。
- **`fixedSubgroup_restrict_eq` / `card_fixedSubgroup_restrict`** (部分群側): L-不変部分群 `N≤H` への
  制限作用 `hN.restrict:L→*MulAut ↥N` (既存 Ch03 `IsAInvariant.restrict`) で
  `fixedSubgroup hN.restrict X = (fixedSubgroup φ X).subgroupOf N` ⟹ `|C_N(X)| = |C_H(X)⊓N|`。
- helper `isAInvariant_comp_subtype` (A-inv の `X≤L` 制限)。

⚠ **naming wart**: 誘導商作用の実名は `OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom`
(Ch04 Main が `namespace Ch04` 内で Ch03 修飾名 `def` ⟹ Ch04 prefix; dot 不可)。一方 `restrict`/
`restrict_apply_val` は Ch03 で正しく宣言され dot OK。clean 化は source の `_root_.` 修飾 = spine 全
rebuild ゆえ別 issue で coordinate (lane-f 領域)。

### 残り group-theoretic assembly (次 pickup, この順)

**A. 最小 L-不変正規 el-ab 存在** (gating, 再利用可・cor (i) も unblock): 非自明有限可解 `H` + L-作用で
   ∃ 非自明 L-不変正規 el-ab `N◁H`。route = (i) `{N:Subgroup H | N≠⊥ ∧ N.Normal ∧ IsAInvariant φ N}`
   は ⊤ を含む非空有限 poset ⟹ 極小元 `N` (mathlib `Finite.exists_min`/well-founded); (ii) N el-ab:
   `⁅N,N⁆` と p-torsion が N の char ⟹ L-不変正規 (helper 要: `IsAInvariant φ ⁅N,N⁆` を
   `IsAInvariant φ N` から — `(φ l)` が ⁅N,N⁆ を保つ; 既存 `IsAInvariant.commutator_self` は全体群版,
   部分群版を書く) ⟹ 極小性で `⁅N,N⁆=⊥` (N abel) + p-torsion=N (exponent p) ⟹ el-ab。
   別 route (極小元回避): 最終非自明 derived `H^(n)` = char abel 非自明 → その p-torsion = char el-ab。

**B. 強帰納 `wielandt_group_formula_of_perfactor`** (`Nat.card H` 上): 非自明なら A で `N` を取り、
   per-factor 恒等式を `N` に (C 経由)、IH を `H/N` (quotientMulAutHom 作用) に適用、
   `card_fixedSubgroup_eq_mul` ×3 (X=⊤/E/U) + `|H|=|N|·|H/N|` で combine。combine 算術 (検算済,
   clean): per-factor `a_⊤^e·|N|=a_E^e·a_U` × IH `b_⊤^e·|H/N|=b_E^e·b_U` ⟹
   `(a_⊤b_⊤)^e·|H| = (a_Eb_E)^e·(a_Ub_U)`, ここで `|C_H(X)|=a_X·b_X` (multiplicativity), e=|E|。
   base `H=1` 自明。**per-factor を hypothesis 化して (†) を isolate**。

**C. per-factor 恒等式の discharge**: `card_fixedSubgroup_restrict` (a_X=|C_N(X)|) +
   `card_fixedSubgroup_wielandt_of_dim` (el-ab N の作用 hN.restrict, modulo (†) dim 恒等式 hdim)。
   hdim = `WielandtCounting.finrank_elab_identity` (modulo (†))。

**D. (†) module wiring** (lane-f coupled rep-theory, resume⁵ NEXT 0-3): hdim を done engine 群から。

**E. architecture relocation**: 最終 `wielandt_fixedPoint_frobenius` は `CoprimeAction.lean` (statement+
   carrier `CoprimeFrobeniusAction`+3 corollary) にあるが、real proof は `WielandtElabBridge`
   (CoprimeAction の下流) を要す ⟹ statement+carrier を downstream leaf へ再配置 + 消費側 S11/S15 の
   import 更新が要る (CoprimeAction は CoprimeFixedPoints を import 不可=循環)。B+C は CoprimeFixedPoints
   下流の新 leaf に置き、E でそこへ wielandt_fixedPoint_frobenius を移す。

## 2026-06-21 (lane-h resume²cont) — 群論層 完全完成 (toolkit + A + step + assembly)

**✅✅✅✅✅ (9.1) chief-series assembly の群論的層が全 axiom-clean で完成** (5 leaf-lemma, full build
3875 green, AxiomsCheck 全登録)。`wielandt_fixedPoint_frobenius` は群論的に完全還元され、残りは
表現論的 (†) のみ:

| lemma | file | 内容 |
|---|---|---|
| `card_fixedSubgroup_eq_mul` | CoprimeFixedPoints | `\|C_H(X)\|=\|C_H(X)⊓N\|·\|C_{H/N}(X)\|` (商側, Cor 3.28) |
| `card_fixedSubgroup_restrict` | CoprimeFixedPoints | `\|C_N(X)\|=\|C_H(X)⊓N\|` (部分群側, `IsAInvariant.restrict`) |
| `wielandt_step` | CoprimeFixedPoints | per-factor + IH ⟹ 群レベル恒等式 (1 chief step) |
| `exists_aInvariant_normal_isElementaryAbelian` | MinimalInvariantNormal | A: 非自明可解 H に el-ab L-不変正規 N◁H 存在 |
| `wielandt_formula_of_perfactor` | WielandtAssembly | B: `WielandtPerFactor L U E` ⟹ 群公式 (`Nat.card H` 強帰納) |

**還元の鎖**: 群公式 ⟸ `WielandtPerFactor L U E` (B, axiom-clean) ⟸ universal per-factor 恒等式 (C,
未) ⟸ (†) per el-ab chief factor (D=lane-f rep-theory)。

### 残り (この順)

**C. per-factor discharge** (`WielandtPerFactor L U E` を提供): 各 el-ab N で
`card_fixedSubgroup_wielandt_of_dim` (WielandtElabBridge, V=↥N, φ=hN.restrict, module =
`IsElementaryAbelian.zmodModule`) + `card_fixedSubgroup_restrict` (3×, `\|fixedSubgroup hN.restrict X\|
=\|C_H(X)⊓N\|`) を合成 ⟹ per-factor 恒等式。dim 恒等式 `hdim` (= `finrank_elab_identity` modulo (†)) を
universal hypothesis 化すれば C も axiom-clean (gate=(†))。**新 leaf は WielandtElabBridge + WielandtAssembly
を import** (両者 independent branch, 循環なし)。fiddly 点 = `elabRepresentation (hN.restrict)` の
invariants と `fixedSubgroup hN.restrict` の card 整合 + module instance 配線。

**D. (†) module wiring** (lane-f coupled rep-theory, resume⁵ NEXT 0-3): `hdim`/`htag` を done engine 群
(centerProj isotypic + free-orbit + base change) から discharge。

**E. relocation**: `wielandt_fixedPoint_frobenius` (CoprimeAction.lean:160) を C を import する downstream
leaf へ移し、`wielandt_formula_of_perfactor` + C で sorry-free 化。statement+carrier `CoprimeFrobeniusAction`
+3 corollary を移動、消費側 S11/S15 の import 更新 (CoprimeAction は CoprimeFixedPoints 等を循環で import 不可)。

⚠ universe: B は型可変強帰納ゆえ `theorem ….{u}` + `WielandtPerFactor.{_, u}` + `∀ (H : Type u)` で
H 宇宙を統一 (`∀ (H : Type _)` だと fresh 宇宙で `hpf H` が mismatch)。C も同様の注意要。

## 2026-06-21 (lane-h resume³) — piece C DONE (per-factor discharge, axiom-clean)

**✅✅ piece C 完成** (新 leaf `OddOrder/GroupTheory/WielandtPerFactorDischarge.lean`, sorry-free +
axiom-clean, AxiomsCheck 登録, full build 3876 green, 実 sorry 137 不変 = 設計通り)。commit `7423193a`。

`WielandtPerFactor L U E` を **dim 恒等式 (⋆) を hyp 化**して produce する配線が完成。鎖:
群公式 ⟸ `WielandtPerFactor` (B✅) ⟸ `wielandtPerFactor_of_dim` (C✅) ⟸ per-factor (⋆)
`PerFactorDimIdentity` (= D の obligation, (†) gate) ⟸ (†) per chief factor (D=lane-f, 未)。

新 leaf の構成:
- `WielandtDimIdentity {V} [CommGroup V] (p) [Module (ZMod p) (Additive V)] (ρ) (U E) [Fintype E]` —
  抽象 𝔽_p-表現の dim 恒等式 (⋆)。`finrank_elab_identity` の結論形 ((†) modulo)。
- `IsElementaryAbelian.subgroupCommGroup`/`subgroupZmodModule` — `↥N` の canonical 𝔽_p-構造。
- `PerFactorDimIdentity φ hN p hpe` — (⋆) を `V = ↥N` (制限作用 `hN.restrict`) に特殊化。**piece D の証明対象**。
- `wielandtPerFactor_of_dim.{u} [Fintype E] (hdim : ∀ …, PerFactorDimIdentity …) : WielandtPerFactor.{_,u}`
  — `card_fixedSubgroup_wielandt_of_dim` (dim→card on ↥N) + `card_fixedSubgroup_restrict`×3
  (`|C_N(X)|=|C_H(X)⊓N|`) で配線。

### ⚠⚠ 重要な instance 知見 (piece D も必ず踏む — `↥N` を 𝔽_p-加群に見る詰みどころ)

`↥N` (subgroup 型) は canonical な**非可換** `Group ↥N` を持つため、`Additive ↥N` の additive 構造が
ダイヤモンドになり `↥(Submodule …)` coercion が壊れる。`finrank_elab_identity`/`card_fixedSubgroup_*`
は `↥(elabRepresentation …).invariants` を coerce するのでこれを踏む。2 段で回避:

1. **CommGroup は canonical Group の上に直に構築** (`{ (inferInstance : Group ↥N) with mul_comm := hpe.comm }`)
   — `CommGroup.toGroup = N.mul` (canonical) ゆえ `MulAut ↥N` が `hN.restrict` と一致。
   PRank の `IsElementaryAbelian.zmodModule` (= `IsMulCommutative` 経由) は **使わない** — その内部
   AddCommGroup が canonical と別で coercion がダイヤモンドる。module は `AddCommGroup.zmodModule`
   (`[NeZero p]` 不要) で**この canonical CommGroup の上に**直構築 (`subgroupZmodModule`)。
2. **dim 恒等式は module を instance *binder* に持つ別 def `WielandtDimIdentity` で書く** — coercion は
   binder に対し**一度だけ**解決され、`↥N` の concrete module を**代入**しても壊れない。直接 `letI`-module
   の上で `↥(Submodule …)` を書くと coercion が壊れる (`Module.finrank (ZMod p) (Additive ↥N)` は letI でも
   通るのに `↥Submodule` だけ壊れるのが罠; probe で確認)。`card_fixedSubgroup_wielandt_of_dim` 自体が
   binder-def ゆえ、これに渡す分には問題ない (適用は代入)。
   - 補足: scoped instance `[Group G][IsMulCommutative G] → CommGroup G` は `open scoped IsMulCommutative`
     で発火するが priority 50 + coercion 解決では効かず `↥Submodule` は救えない (probe 済)。

⚠ universe: piece B 同様 `wielandtPerFactor_of_dim.{u}` + `∀ (H : Type u)` + `WielandtPerFactor.{_,u}`。
⚠ `PerFactorDimIdentity φ hN p hpe` は `U E` を引数で受けない (section 暗黙) ので hyp 内で `(U := U) (E := E)`
   明示 pin が要る (さもないと `Fintype E` が metavar 化して stuck)。

### 残り (この順) — piece C 完了後

**D. (†) module wiring** (lane-f coupled rep-theory, resume⁵ NEXT 0-3): `PerFactorDimIdentity φ hN p hpe`
(= `WielandtDimIdentity p hN.restrict U E` modulo 上記 letI 構造) を per chief factor で証明。中身 =
`finrank_elab_identity` (要 `hUE: U⊔E=⊤` + `htag` (†)) を `elabRepresentation p hN.restrict` に適用し
done engine 群 (centerProj isotypic + free-orbit + base change) で `htag` を discharge。上記 instance 知見を
そのまま流用。`hUE` は Frobenius 構造から。`Invertible (Fintype.card U : ZMod p)` は coprimality + p 素数。

**E. relocation** — `wielandt_fixedPoint_frobenius` (`CoprimeAction.lean:156`, sorry) を C import 可能な
downstream leaf へ移し `wielandt_formula_of_perfactor` + `wielandtPerFactor_of_dim` で sorry-free 化。
⚠ entangle 注意: carrier `CoprimeFrobeniusAction` + 3 corollary + FrobeniusCentralizer 節
(`isFrobenius_kernel_eq_bot_of_frobenius_subgroup` 等) が **CoprimeAction 内で carrier を使用**しているので
それらも一緒に移す必要がある (`fixedSubgroup` def 自体は多数 import 元ゆえ CoprimeAction に残す)。消費側
S11/S15 の import 更新も。spine refactor ゆえ要計画。**D 無しでは sorry は減らない** (E は配線のみ)。
