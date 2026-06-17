# Peterfalvi (9.1) Wielandt fixed-point formula — proof design (lane-f, 2026-06-17)

## Status

- ✅ **Faithful redesign + corollaries DONE** (`CoprimeAction.lean`, commit `c55f6db2`,
  build-green + AxiomsCheck OK). 3 sorries → 1.
  - `CoprimeFrobeniusAction` now carries a real action `φ : L →* MulAut H`; the three
    fixed subgroups are *derived* (`fixedByUE/E/U = fixedSubgroup φ ⊤/E/U`), so the
    statements are genuine.
  - Both corollaries proved from the main formula (antitone fixed points +
    `Subgroup.eq_top_of_card_eq`).
- ❌ **Main `wielandt_fixedPoint_frobenius` = the sole remaining sorry.**

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
1. Specialise the orbit equality to a cyclic `⟨e⟩`. Cleanest: generalise to an arbitrary acting
   group via a hom `ψ : Γ →* MulAut G` — `centerRep'.comp ψ : Representation k Γ (CenterCarrier k G)`
   (a `Representation` IS a `MonoidHom` to `Module.End`, so `MonoidHom.comp` typechecks), apply the
   cornerstone twice (class-sum + idempotent) ⟹ `#(Γ-orbits on classes) = #(Γ-orbits on simples)`.
   Then take `Γ = ↥(Subgroup.zpowers e)` (or a cyclic group) with `ψ = Subgroup.subtype`.
2. Glauberman coprime-FPF (repo `glauberman_fixed_points_conj`): every `e^j` (`1≤j<d`) is FPF on `U`
   ⟹ fixes only the trivial class ⟹ `⟨e⟩` free on the `Ncl−1` nontrivial classes ⟹
   `#orbits-classes = 1 + (Ncl−1)/d`.
3. Transfer via the Brauer equality + `Nsimples = Ncl` ⟹ `#orbits-simples = 1 + (Ncl−1)/d` ⟹ every
   nontrivial-simple orbit has size `d` ⟹ `⟨e⟩` (hence `E`) acts freely on the nontrivial simples ⟹
   feed I-3 ⟹ (†).

`Nsimples = Ncl`: `idemBasis` is indexed by `Fin N` and `centerBasis` by `ConjClasses G`, both bases
of the same `Z(k[G])`, so `N = #(ConjClasses G)` (equal `finrank`) — the `dim`-equality, not a
separate fact.

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
