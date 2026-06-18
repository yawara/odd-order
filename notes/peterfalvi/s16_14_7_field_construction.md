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

1. **`U`-irreducibility on `P`** — new lemma per the argument above. Needs `Maschke` (mathlib has
   `RepresentationTheory/Maschke.lean`) + constituent-Singer + the primitive-prime fact. ⚠ The
   `u = q^k` exceptional case needs number theory; **Zsygmondy is likely not in mathlib** (only
   primitive-roots/cyclotomic files) so this step may need an elementary special-case proof or a
   small Zsygmondy fragment. Input `u=(p^q-1)/(p-1)` comes from (14.7)'s arithmetic (already done).
2. **`P` as `F_p[U]`-module** from the conjugation action (`IsElementaryAbelian p P` ⟹ `ZMod p`-module;
   U-conjugation is `F_p`-linear). Build the `Module (MonoidAlgebra (ZMod p) ↥U) ↥P` directly.
3. **Apply Singer engine** → `P ≃+ GF(p^q)`, `U → GF(p^q)ˣ`.
4. **σ assembly** — build `sigma : GF(p^q)⋊U* →* G` matching `P`/`U`/`W₂`, using (not modifying)
   the frozen Core defs (`fieldNormalizerFrobeniusGroup`, `fieldNormalizerKernel`, …). Heavy but
   ungated.
5. **part (14.2)(b)** — `Q` elem abelian, `W₂` normalizes `Q`, `∃ y∈Q` — via (13.2.b)/(14.5).
   **This is the only §13-gated piece** (and is a small structural read-off in the textbook).

`exists_LHypothesis`/`exists_MHypothesis` (14.3/14.10) and the case-B cascade remain Dade-gated
(Lane B's §3-13 character theory), independent of the above.

## FT connection (verified)

`feitThompson → noMinimalSimpleOdd_of_section16 → BG.AppC.final_contradiction →
S16.nonexistence_of_G → S16.field_normalizer_structure → field_normalizer_of_U_characteristic`.
So closing (14.7) genuinely reduces `feitThompson`'s transitive `sorry` closure (POLE-2 is on the
critical path; it is *not* orphaned the way (6.8) currently is).
