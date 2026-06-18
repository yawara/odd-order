# Peterfalvi (14.7) field-normalizer construction — design + roadmap

Lane H, 2026-06-18. Tracks POLE-2 (`issues/pending/2009-s16-field-normalizer-pole2.md`).

## What (14.7) needs (the genuine hard core of POLE-2)

`field_normalizer_of_U_characteristic` (`S16_NonExistenceG.lean`, the `sorry` after the
`cyclotomic` arithmetic) must produce `Nonempty (FieldNormalizerData hyp)`, whose core is

* `sigma : fieldNormalizerFrobeniusGroup hyp →* G` (injective) where
  `fieldNormalizerFrobeniusGroup = GF(p^q) ⋊ U*` (frozen Core `S16_NonExistenceGCore`),
* `sigma_P_eq_P`, `sigma_U_eq_U`, `sigma_P0_eq_W2` — the field isomorphism **(14.2)(a)**,
* `cyclotomic_coprime` (✅ have via `cyclotomic_quotient_coprime_of_not_dvd`),
* part **(14.2)(b)**: `Q_elementaryAbelian`, `W2_normalizes_Q`, `∃ y ∈ Q, W₂^y normalizes U`.

The textbook (14.7) proof only does the **arithmetic** (`u = (p^q-1)/(p-1)` via the FPF
congruence `q ≡ 1+p+…+p^{q-1} ≡ 1 mod p`, contradicting `q<p`) and reads (a)/(b) off
standing structure. In the Lean formalization the field iso (a) must be **constructed**.

## CORRECTED diagnosis (2026-06-18): (14.2)(a) is NOT gated on §11-13

Prior sessions called (14.7) "deeply gated on §13 type-I structure / GaloisField construction
/ a big multi-session thing". On re-reading the math this is **wrong for part (a)**.

The field structure is the **Singer mechanism**: an irreducible `F_p`-linear action of a
cyclic group on an elementary-abelian `p`-group makes it a field, with the group inside the
multiplicative group. The only nontrivial input is **U acts irreducibly on P**, and that is
**provable from the hypothesis**, not a §11-13 import:

* `c_eq_one` (`S15_SAndT.lean:523`) ⟹ `C = U ⊓ C_G(P) = 1` ⟹ **U acts faithfully on P**.
* U is **cyclic**, `|U| = u = (p^q-1)/(p-1)` (from (14.7)'s arithmetic), `|P| = p^q`, `dim_{F_p} P = q`.
* Maschke (coprime: `gcd(u,p)=1`) ⟹ `P = ⊕ Pᵢ` as `F_p[U]`-modules; U faithful + cyclic ⟹
  `u = lcm(uᵢ)` where `uᵢ` = order of U on the irreducible constituent `Pᵢ`.
* On each irreducible `Pᵢ` (dim `dᵢ`), `End_{F_p[U]} Pᵢ = F_{p^{dᵢ}}` (Singer/Schur), so `uᵢ ∣ p^{dᵢ}-1`.
* A prime `r ∣ u`: `order_r(p) ∣ q` (q prime) so `=1` or `=q`. `order=1 ⟹ r ∣ p-1`, but
  `u ≡ q (mod p-1)` so then `r ∣ q ⟹ r = q`. Hence **every prime `r ∣ u`, `r ≠ q`, is a
  primitive prime divisor** (`order_r(p)=q`, so `r ∤ p^{dᵢ}-1` for `dᵢ<q`). Since `u = lcm(uᵢ)`
  with each `uᵢ ∣ p^{dᵢ}-1`, such an `r` forces some `dᵢ = q` ⟹ single constituent ⟹ **P irreducible**.

So (14.2)(a) reduces to a self-contained representation-theory + elementary-number-theory
argument. The genuinely §13-gated part is only (14.2)(b) (Q's structure, `y`, via (13.2.b)/(14.5)).

## ✅✅ DONE: the entire abstract (14.2)(a) machinery (2026-06-18)

`OddOrder/GroupTheory/RepresentationTheory/SingerField.lean`, all sorry-free + axiom-clean:

* `nonempty_singerFieldData` / `card_K_eq` / `nonempty_ringEquiv_galoisField` (Singer engine, `3b8b7204`)
* `cyclotomicQuotient_not_dvd_pow_sub_one` (number-theory core, `c4622552`)
* `pow_sub_one_dvd_of_dvd`, `not_dvd_factorial_pred` (helpers)
* **`isSimpleModule_of_isCyclic_faithful_card`** (Singer irreducibility keystone, `9043df39`):
  faithful cyclic `C` of order `(p^q-1)/(p-1)` acting on `F_p`-module of order `p^q` ⟹ simple.
  Needs only `[Module (MonoidAlgebra (ZMod p) C) M]` + `[NeZero (card C : ZMod p)]` (the dual
  `ZMod p`/scalar-tower structure turned out unused — Maschke supplies it via `restrictScalars`).
* **`exists_galoisField_repr`** (abstract (14.2)(a), `4bdedb49`): same hypotheses ⟹
  `∃ e : M ≃+ GaloisField p q, ∃ μ : C →* (GaloisField p q)ˣ, Injective μ ∧ e (of c • x) = μ c · e x`.

⟹ **steps 1 and 3 are complete.** The remaining (14.7) work is purely FT-specific wiring,
and it depends on §13/§15 producers (see "Remaining" below).

## ✅ Done: the Singer engine (commit `3b8b7204`)

`OddOrder/GroupTheory/RepresentationTheory/SingerField.lean` — sorry-free, axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

* `SingerFieldData ρ` / `nonempty_singerFieldData`: abelian `C` simple over `F_p[C]` ⟹ field
  `K`, `e : M ≃+ K`, `μ : C →* Kˣ`, `e (of c • m) = μ c * e m`. Commutative-ring route
  (`isSimpleModule_iff_quot_maximal` + `Ideal.Quotient.field`); **no Wedderburn/Jacobson**.
* `card_K_eq` (|K|=|M|), `nonempty_ringEquiv_galoisField` (`K ≃+* GF(p^n)` when `|M|=p^n`).
* Stated over `M` **directly** an `F_p[C]`-module (NOT `Representation.asModule`) — `asModule`'s
  `Module` instance fails tactic-mode synthesis here (noncomputable + synonym reducibility);
  term-mode synth works but `inferInstance`/`rw` inside `by` do not. Direct `M` sidesteps it.

## Remaining road to closing (14.7) (concrete, mostly ungated)

1. **`U`-irreducibility on `P`** — new lemma per the argument above.
   - ✅ **number-theory core done**: `cyclotomicQuotient_not_dvd_pow_sub_one` (commit `c4622552`,
     `SingerField.lean`): `q` prime, `q∤D` ⟹ `(p^q-1)/(p-1) ∤ p^D-1` (no Zsygmondy — pure gcd:
     `Nat.pow_sub_one_gcd_pow_sub_one` gives `u ∣ p^{gcd(q,D)}-1 = p-1`, but `u > p-1`).
   - **remaining rep-theory step** (the keystone): clean argument avoiding `orderOf = lcm` —
     suppose `P` not simple; Maschke ⟹ `IsSemisimpleModule`; `exists_sSupIndep_sSup_simples_eq_top`
     ⟹ finite family of simple submodules `Sᵢ` with `⨆ Sᵢ = ⊤`; each `Sᵢ ≠ P` (P not simple) so
     `dᵢ := finrank Sᵢ < q`, hence `q ∤ D := lcm dᵢ`. Apply the **Singer engine to each `Sᵢ`** ⟹
     `Sᵢ ≅` field of order `p^{dᵢ}`, so `(g|Sᵢ)^{p^{dᵢ}-1}=1`, and `dᵢ ∣ D` ⟹ `(g|Sᵢ)^{p^D-1}=1`.
     So `g^{p^D-1}` fixes every `Sᵢ` ⟹ fixes `⨆Sᵢ=⊤` ⟹ `g^{p^D-1}=1` (faithful) ⟹ `u ∣ p^D-1`.
     With `q∤D`, `cyclotomicQuotient_not_dvd_pow_sub_one` gives the contradiction. ⟹ `P` simple.
   - ⚠ **setup caveat**: needs `P` carrying BOTH `Module (ZMod p)` (for `finrank = q`) and
     `Module (MonoidAlgebra (ZMod p) U)` (for the action) with an `IsScalarTower`; applying Singer to a
     `Submodule` `Sᵢ` and reading `finrank Sᵢ` is the fiddly part. ~100-150 lines, own focused build.
     Input `u=(p^q-1)/(p-1)` comes from (14.7)'s arithmetic (already done).
2. ✅ **abstract field structure** — `exists_galoisField_repr` (DONE, see above). Just needs its
   hypotheses supplied.
3. **`P` as `F_p[U]`-module + discharge hypotheses** — the FT-specific wiring:
   - `IsElementaryAbelian p P` ⟹ `ZMod p`-module on `↥P`; `U`-conjugation is `F_p`-linear ⟹
     `Representation (ZMod p) ↥U ↥P` ⟹ `Module (MonoidAlgebra (ZMod p) ↥U) (asModule)`.
     ⚠ asModule tactic-synth trap may resurface — provide the instance explicitly / apply at term level.
   - `Nat.card ↥P = p^q` (from `basic_structure` (13.2), **a sorried §13 producer**),
     `Nat.card ↥U = (p^q-1)/(p-1)` (from (14.7) arithmetic + `c_eq_one`), faithful (`c_eq_one`),
     `NeZero` (|U| coprime to p). ⟹ `exists_galoisField_repr` gives `P ≃+ GF(p^q)`, `U → GF(p^q)ˣ`.
4. **σ assembly** — build `sigma : GF(p^q)⋊U* →* G` matching `P`/`U`/`W₂` from the (14.2)(a) iso,
   using (not modifying) the frozen Core defs (`fieldNormalizerFrobeniusGroup`, `fieldNormalizerKernel`,
   …). Heavy mechanical wiring.
5. **part (14.2)(b)** — `Q` elem abelian, `W₂` normalizes `Q`, `∃ y∈Q` — via (13.2.b)/(14.5).
   §13-gated structural read-off.

**Net**: the genuinely-novel/ungated math of (14.2)(a) is DONE. What's left is FT-specific plumbing
that **bottoms out in the sorried §13/§15 producers** (`basic_structure`, `c_eq_one`, the (14.7)
case arithmetic) — i.e. the same §13 character/structure theory that gates `exists_L/MHypothesis`.

## ✅✅ DONE: σ-bridge (step 4) — `fieldNormalizerData_of_repr` (2026-06-18, commits `aee72713`/`410471ea`/`d948ce69`)

`OddOrder/Peterfalvi/S16_NonExistenceG.lean`, all sorry-free + axiom-clean + AxiomsCheck-registered.
The σ-bridge takes the (14.2)(a) iso as *input* (so it is ungated) and builds `FieldNormalizerData`.

* **`fieldNormalizerKernelTransport` (fN)**: from `e : Additive ↥P ≃+ 𝔽_{p^q}`, the hom
  `𝔽_{p^q} →* G`, `s ↦ ↑(Additive.toMul (e.symm s))`. + `_apply`/`_injective`/`_range` (= P).
* **`fieldNormalizerComplementTransport` (fU)**: from `μ : U →* 𝔽_{p^q}ˣ` (inj, range = normOneUnits),
  the hom `U* →* G` inverting μ + including back (`U.subtype ∘ (corestrict μ).symm`). +
  `_exists` (each `u*` has `v∈U` with `μ v = u*`, `fU u* = ↑v`) / `_injective` / `_range` (= U).
* **`fieldNormalizerData_of_repr`**: `σ := SemidirectProduct.lift fN fU hcompatLift`, glued by the
  (14.2)(a) `U`-equivariance.  Final signature (the actual landed interface):
  ```
  (e : Additive ↥P ≃+ GaloisField p q) (μ : ↥U →* (GaloisField p q)ˣ) (hμ_inj) (hμ_range)
  (hUP : ∀ v x, (v:G)*(x:G)*(v:G)⁻¹ ∈ P)                       -- U normalizes P
  (hcompat : ∀ v x, e (ofMul ⟨(v:G)*(x:G)*(v:G)⁻¹, hUP v x⟩) = (μ v : GF) * e (ofMul x))
  (hW2 : (span_{ZMod p}{1}).toAddSubgroup.toSubgroup.map fN = W₂)  -- prime line ↦ W₂
  (hPU_disj : P ⊓ U = ⊥) (hcyclotomic : Coprime ((p^q-1)/(p-1)) (p-1))
  (hQ_elemAb …)(hW2_norm_Q …)(yQ)(hyQ_mem …)(hW2_conj_y …)                 -- part (14.2)(b)
  : Nonempty (FieldNormalizerData hyp)
  ```
  Properties: `sigma_injective` via `ker = ⊥` (kernel meets complement trivially, `P ∩ U = 1`);
  `sigma_P_eq_P`/`sigma_U_eq_U` via `range_eq_map`+`map_map`+`lift_comp_inl/inr`+transport ranges;
  `sigma_P0_eq_W2` via the prime-line = `inl`-image of `span{1}` reduction to `hW2`.

**Lean gotchas hit** (recorded for reuse): `Multiplicative.toAdd s` infers the *unfolded*
`GaloisField`-as-`SplittingField` type → `HMul` fails against folded `GaloisField` (instance diamond);
fix = annotate `(… : GaloisField p q)` + `set t : GaloisField p q := …`.  TypeTags cancellation
lemmas are **root-namespace** (`toAdd_ofAdd`/`ofAdd_toAdd`/`toMul_ofMul`/`ofMul_toMul`), not
`Multiplicative.*`/`Additive.*`.  `mul_eq_one_iff_eq_inv.mp` for `a*b=1 ⟹ a=b⁻¹`.  The lift
compatibility goal is reached defeq via `show fN (φ u s) = fU u * fN s * (fU u)⁻¹` (avoids fragile
`simp only [comp_apply, …]`).

## ✅✅✅ DONE: step 3 field model + structural inputs (2026-06-19)

`field_normalizer_of_U_characteristic` (S16:790, bare sorry) is now **structured** — both the σ-bridge
(step 4, above) and the (14.2)(a) field model (step 3) plus most σ-bridge hypothesis-inputs are proven:

* **step 3** `exists_pu_field_repr` (`af543785`): from `hu_full : |U| = (p^q-1)/(p-1)` and `[IsCyclic ↥U]`,
  makes `Additive ↥P` an `𝔽_p[U]`-module via conjugation (`Representation = mulAutToEnd ∘ (normalizerMonoidHom
  ∘ inclusion(U≤N(P)))`, module via `Module.compHom` on `ρ.asAlgebraHom` — sidesteps the asModule synth trap)
  and applies `exists_galoisField_repr` ⟹ `e : Additive ↥P ≃+ GF`, `μ : U →* GFˣ`, the compat. Cites
  sorried §13 `basic_structure`(|P|=p^q) + `c_eq_one`(faithful). Diamond notes: `open scoped IsMulCommutative`,
  `AddCommGroup.zmodModule` (not `IsElementaryAbelian.zmodModule`), explicit `CommGroup ↥U` reusing canonical Group.
* **hUP** `conj_mem_P` + `U_le_normalizer_P` (`a6ab11ee`, **unconditional**): `U ≤ N(P)` via `U ≤ S' ≤ S`,
  `P = F(S) ⊴ S` (`maxNilpotentNormalHall_le_normalizer`).
* **hPU_disj** `P_inf_U_eq_bot` (`427e36e9`, §13-cite): `P ⊓ U ≤ U ⊓ C_G(P) = C = 1` (P abelian + `c_eq_one`).
* **hμ_range** `mu_range_eq_normOneUnits` (`c83540d7`, **unconditional**): inj `μ` with `|U|=(p^q-1)/(p-1)`
  ⟹ `μ.range = normOneUnits` (both = unique order-d subgroup `ker(powMonoidHom d)` of cyclic GFˣ,
  `IsCyclic.card_powMonoidHom_ker` gives card = gcd = d).
* **hcyclotomic** `cyclotomic_quotient_coprime_of_not_dvd` (existing): given `q∤(p-1)`.

## ✅✅ hW2 scaling DONE + assembly verified (2026-06-19, `b2564baf`)

The one piece deferred at the 2026-06-19 depletion stop — the **hW2 scaling** — is **done**, and the
full σ-bridge assembly is verified `sorry`-free as an engine. Three lemmas (full build 3863 jobs ~32s
green, real sorry 140 unchanged):

* **`field_repr_rescale_to_W2`** — *axiom-clean* (`[propext, Classical.choice, Quot.sound]`, no §13 cite).
  Takes the generic model `(e₀, μ, hcompat₀)` + `W₂ ≤ P`; pick `w₀ ∈ W₂` (≠1, `|W₂|=p`),
  `c := e₀(ofMul w₀) ≠ 0`, build the `×c⁻¹` `AddEquiv` *by hand* (`mul_inv_cancel_left₀`/`inv_mul_cancel_left₀`/
  `mul_add` — sidesteps the missing `DistribMulAction.toAddEquiv₀`), `e := e₀.trans scale`. Then `e(ofMul w₀)=1`.
  hW2 proof: `Span = (span 𝔽_p{1}).toAddSubgroup.toSubgroup = Subgroup.zpowers (Multiplicative.ofAdd 1)`
  (le_antisymm; `Multiplicative.mem_toSubgroup` + `Submodule.mem_span_singleton`; ZMod p-linearity via
  `r•x = r.val•x` = `Nat.cast_smul_eq_nsmul` + `ZMod.natCast_rightInverse`; `ofAdd_nsmul`, `ofAdd_toAdd`),
  then `MonoidHom.map_zpowers` ⟹ `Span.map fN = zpowers (fN(ofAdd 1)) = zpowers (↑w₀)`, and
  `zpowers ↑w₀ = W₂` since `orderOf ↑w₀ = p` (prime, `OneMemClass.coe_eq_one`/`orderOf_dvd_natCard`),
  `Subgroup.eq_of_le_of_card_ge`. compat survives by field commutativity (`ring`).
* **`exists_pu_field_repr_W2`** (§13-cite) — chains `exists_pu_field_repr` + the rescaling → full
  `(e, μ, hμ_inj, hcompat, hW2)` package.
* **`field_normalizer_of_U_characteristic_of_inputs`** (literal-`sorry`-free) — assembly engine taking the
  §13/§14 facts as explicit hypotheses; calls `exists_pu_field_repr_W2` + `mu_range_eq_normOneUnits` +
  `conj_mem_P` + `P_inf_U_eq_bot` + `fieldNormalizerData_of_repr`. **Verifies the whole σ-bridge typechecks.**

⟹ `field_normalizer_of_U_characteristic` is now reduced to *producing* `_of_inputs`'s named obligations
(docstring records the recipe). **The ungated field-algebra runway is exhausted.**

### Remaining (all pure §13/§14, Lane B / §14 counting)

1. **value-argument** `|U| = (p^q-1)/(p-1)` + `q∤(p-1)` — (13.15) `caseB_order_u` dichotomy + the `p≡1 mod q`
   case killed by **W₂^y acting FPF on U ⟹ u ≡ 1 mod p** (then `q ≡ qu ≡ 1 mod p`, contra `q<p`). FPF fact
   uses part(b)'s `y`, **§14-structural, not formalized**.
2. **`[IsCyclic ↥U]`** — §13 standing fact (can't derive from the field model: `exists_pu_field_repr` *requires* it).
3. **`W₂ ≤ P`** — §13-structural (`FieldNormalizerData.W2_le_P` is a *data* projection ⟹ circular; needs an
   independent producer from the §13/§15 structure).
4. **partB** — `Q` elem abelian / `W₂` normalizes `Q` / `∃y∈Q` via (13.2.b)/(14.5) (**§13** cite).
5. **close** — feed (1)-(4) + `IsCyclic` to `field_normalizer_of_U_characteristic_of_inputs`.

`exists_LHypothesis`/`exists_MHypothesis` (14.3/14.10) and the case-B cascade remain Dade-gated (Lane B's
§3-13 character theory), independent of the above.

## FT connection (verified)

`feitThompson → noMinimalSimpleOdd_of_section16 → BG.AppC.final_contradiction →
S16.nonexistence_of_G → S16.field_normalizer_structure → field_normalizer_of_U_characteristic`.
So closing (14.7) genuinely reduces `feitThompson`'s transitive `sorry` closure (POLE-2 is on the
critical path; it is *not* orphaned the way (6.8) currently is).
