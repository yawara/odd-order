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

## σ-bridge construction plan (step 4, scoped 2026-06-18 — ungated, intricate frozen-Core)

The σ-bridge takes the (14.2)(a) iso as *input* (so it is ungated) and builds `FieldNormalizerData`.
Target shape:
```
theorem fieldNormalizerData_of_repr (hyp : Hypothesis (G := G))
    (e  : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
    (μ  : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ) (hμinj : Injective μ)
    (hμrange : μ.range = normOneUnits …)                       -- image = U*
    (hcompat : e (Additive.ofMul (conj u • x)) = μ u • e x)    -- (14.2)(a) compat
    (partB …) : Nonempty (FieldNormalizerData hyp)
```
Core facts (all in `OddOrder/BG/AppC_NormSet.lean`, frozen — *use*, don't modify):
* `normOneFrobeniusGroup p q = additiveFieldGroup p q ⋊[normOneMulAction] normOneUnits p q`,
  `additiveFieldGroup = Multiplicative (GaloisField p q)`, complement `normOneUnits` = norm-one
  subgroup of `GF^×` (order `(p^q-1)/(p-1)` = `U*`).
* `normOneFrobenius_conj_inl` : conjugation of an `inl`-kernel point by `inr u` = field-mult by `u`
  — this is exactly the `SemidirectProduct.lift` compatibility, fed by `hcompat`.
Construction:
1. `f_N : Multiplicative (GF) →* G`, `ofAdd s ↦ ↑(e.symm s)` (uses `Additive`/`Multiplicative`
   adjunction: `↥P` multiplicative in `G` ↔ `Additive ↥P` the `F_p`-space `e` lives on).
   `map_mul` ⟸ `e.symm` additive + `↑(x+y : Additive ↥P) = ↑x * ↑y` in `G`. range `f_N = P`.
2. `f_U : normOneUnits →* G`, `u* ↦ ↑(μ.symm-onto-range u*)` (via `hμrange`, `U* ≃ U`). range `= U`.
3. `sigma := SemidirectProduct.lift f_N f_U <compat from normOneFrobenius_conj_inl + hcompat>`.
4. Properties: `sigma_P_eq_P`/`sigma_U_eq_U` from `range f_N = P`/`range f_U = U` + `lift_inl`/`lift_inr`;
   `sigma_P0_eq_W2` from `e`(prime line `F_p ⊆ GF`) `= W₂` (needs `e` to send the prime field to `W₂`
   — extra `hcompat`-style hypothesis on the prime line); `sigma_injective` from `f_N`,`f_U` inj +
   kernel∩complement = ⊥ (`fieldNormalizerKernel_inf_complement_eq_bot`, already in Core).
⚠ The `Additive`/`Multiplicative` bookkeeping (steps 1-2) is the main friction. Estimate ~150-250
lines. Then `field_normalizer_of_U_characteristic` = `fieldNormalizerData_of_repr` ∘
(`exists_galoisField_repr` applied to `Additive ↥P` as `F_p[U]`-module via conjugation) — the latter
needs `|P|=p^q` (`basic_structure`), `|U|=u`, `c=1` (`c_eq_one`): **the §13 gate**.

`exists_LHypothesis`/`exists_MHypothesis` (14.3/14.10) and the case-B cascade remain Dade-gated
(Lane B's §3-13 character theory), independent of the above.

## FT connection (verified)

`feitThompson → noMinimalSimpleOdd_of_section16 → BG.AppC.final_contradiction →
S16.nonexistence_of_G → S16.field_normalizer_structure → field_normalizer_of_U_characteristic`.
So closing (14.7) genuinely reduces `feitThompson`'s transitive `sorry` closure (POLE-2 is on the
critical path; it is *not* orphaned the way (6.8) currently is).
