# Peterfalvi §12 = `S14_MaximalI.lean` — Maximal Subgroups of Type I

> Source: `references/peterfalvi/04.14_pp_69_74_Maximal_Subgroups_of_Type_I.mmd`
> (Peterfalvi numbers the results **(12.1)–(12.17)**; the file is "S14" because it is the
> 14th section of Part I).  Owner: **lane-h**.  Created 2026-06-22 (lane-h resume⁸).

## Headline result

**(12.7) Theorem.** Every maximal subgroup `M` of Type I is a Frobenius group with kernel
`M_F`.  Consumed by **S15** (`typeI_frobenius`, `S15_SAndT:1203/1679`) and underlies
**(12.17) `theorem88_caseB_holds`**, the §14 keystone consumed by the **FT spine**
(`FeitThompson.lean:332`, kills the "every maximal subgroup is Type I" branch).

## Proof structure and lane split

`(12.7)` is proved by a minimal counterexample `(12.8)`–`(12.16)`:

| result | content | lane | notes |
|---|---|---|---|
| (12.1) | Hypothesis: `S`, `τ` Dade isometry | — | setup |
| (12.2)–(12.5) | Dade decomposition / orthogonality / `ρ`-constancy | **B** (char) | opaque-Prop scaffold |
| (12.6) | `L` Frobenius ⟹ `S` coherent | **B** (char, (6.8)) | wired via `S10_CoherenceWiring` |
| (12.8) | minimal counterexample hypothesis | **H** | `CounterexampleHypothesis` (opaque Props) |
| **(12.9)** | `P_0` abelian rank 2; witness `L`, `x` | **H** | needs **(8.12.a)** [absent], (8.17.a)✓, (8.11)✓, [BG]1.16✓, (8.12.b)✓ |
| **(12.10)** | witness `L` Frobenius (kernel `L_F`) | **H/B** | needs (8.16), **(10.10)**, (11.9.c), (11.6), (9.7.b), (8.6.a), (8.3) — type-classification heavy |
| **(12.11)** | `M∩L` complements `K`; `M∩L ⊆ H` | **H** | needs **(8.13.c1)** [absent], (8.1.b/c), and **(9.1) Wielandt** (lane-h ✓, via `wielandt_fixedPoint_trivial_E_fixed`) |
| **(12.12)** | complement `E` cyclic, `e ∣ p−1` or `p+1` | **H** | needs (12.9)–(12.11), **[BG] Thm 2.6(a)** (`odd_two_dim_abelian`, S02, proved✓), Singer field |
| (12.13)–(12.16) | Dade calc + final contradiction | **B** (char) | norm inequality |
| (12.17) | all-Type-I impossible ⟹ (8.8)(b) | **H** assembly | needs (12.7), **(7.11)** (char), (8.17), (2.3) |

## ⚠ Cross-lane gating (the binding constraint)

The lane-h structural chain (12.9)–(12.12) is **gated on §8 facts that are BG §16 consequences
and are NOT extracted in the repo**:

- **(8.12.a)** "every Sylow of `U` is abelian of rank ≤ 2" — needed by (12.9) for `P_0` rank 2.
  S10 has only **(8.12.b)** (`typeI_or_typeII_centralizer_unique`).
- **(8.13.c1)** "`L = L_F ⋊ (M∩L)` and `C_G(x) = C_{L_F}(x) ⋊ C_M(x)`" — needed by (12.11) for
  "`M∩L` complements `K`".  S10's (8.13) (`escapingCentralizers_control`) gives (8.13.b/c4)
  [unique maximal of type I/II] but **not** (8.13.c1).
- (8.1.b)/(8.1.c) — needed by (12.11)/(12.10); partially in `TypeFData`.

⟹ To prove (12.9)/(12.11), lane-h must first **state these as faithful obligations**
(citing BG §16) in S14 — they are lane-b/lane-f territory, so this is the standard
"cite faithful sorried §8 fact" pattern.  The structures `CounterexampleHypothesis` /
`RankTwoWitnessData` also need **faithful-izing** (they carry opaque `Prop` fields with no
`_holds`, so the lemmas are currently vacuous/unprovable as stated).

## ✅ Landed (2026-06-22 lane-h resume⁸)

**`isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`** in
`GroupTheory/RepresentationTheory/SingerField.lean` (sorry-free, axiom-clean
`[propext, Classical.choice, Quot.sound]`):

> A (commutative) group `C` acting `𝔽_p`-linearly, faithfully, and **irreducibly**
> (`M` a simple `𝔽_p[C]`-module) on a finite module `M` is **cyclic**, with
> `|C| ∣ |M| − 1`.

Proof: `nonempty_singerFieldData` realizes `M ≅ K` (field), `μ : C →* Kˣ` injective by
faithfulness; `Kˣ` cyclic ⟹ `C` cyclic; `|C| = |range μ| ∣ |Kˣ| = |K|−1 = |M|−1`.
`Finite C`, `IsCyclic C`, `Fact p.Prime` all **omitted** (derived / unneeded).

This is the **field-theoretic core of (12.12)'s irreducible case** (`|E| ∣ p²−1`) and the
order half of **(14.2)(a)**.  Reusable; deferred-payoff (consumed once (12.12) is assembled).

## ✅✅ RESOLVED (2026-06-22 lane-h resume⁹, commit `6e9fa0a0`) — the instance blocker is gone

**`isCyclic_and_card_dvd_of_faithful_irreducible_comm`** in `SingerField.lean` (sorry-free +
axiom-clean, AxiomsCheck-registered): a finite group `E` acting **faithfully + irreducibly
(`IsSimpleModule (𝔽_p[E]) M`) + commutatively** (commutativity as a *proof*
`hcomm : ∀ a b, a*b = b*a`, **not** a `CommGroup` instance) on a finite module `M` ⟹ `E` cyclic
and `|E| ∣ |M| − 1`.

> **The whole instance-engineering blocker below is solved.**  BG 2.6(a)'s `Std.Commutative`
> output now feeds straight in via `.comm` — no `CommGroup E`, no `MonoidAlgebra`-as-`CommRing`
> instance, no `letI`-shadowing.

**Working route (after two dead ends, see blocker notes below):** for abelian `E` the group
algebra `𝔽_p[E]` *is* commutative (`mul_comm_monoidAlgebra_of_comm`, double `induction_linear`),
so equip it with a `CommRing` built **on top of its existing `Ring`**:
`letI : CommRing _ := { (inferInstance : Ring _) with mul_comm := … }` (no diamond — the `Ring`
is reused).  Then `M` simple ⟹ `M ≅ 𝔽_p[E] ⧸ I` (`isSimpleModule_iff_quot_maximal`), `I` maximal,
`K := 𝔽_p[E] ⧸ I` a field (`Ideal.Quotient.field`); `μ : E ↪ Kˣ` via
`(Units.map (mk).toMonoidHom).comp (of …).toHomUnits`, injective by `hfaith` + the
`map_smul`/`Algebra.smul_def`/`Ideal.Quotient.algebraMap_eq` compat; `Kˣ` cyclic ⟹ `E` cyclic;
`|E| ∣ |Kˣ| = |K| − 1 = |M| − 1` (`Nat.card_units`, `Nat.card_congr lequiv`).

⚠ **Two ruled-out routes (do not retry)**: (a) reusing the `[CommGroup C]`-based
`isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible` — every CommGroup-instance bridge
fails (blocker notes below). (b) realizing the field as `End_{𝔽_p[E]}(M)` via Schur
(`Module.End.instDivisionRing`) + little Wedderburn — **catastrophic Monoid diamond** between
`Module.End.instMonoid` and the division-ring instance's monoid (hard type mismatch at the
`Units.coeHom`/`isCyclic_of_injective_ringHom` seam + `whnf` timeout even at 800k heartbeats).

## ✅✅✅ (12.12) irreducible (Case B) core LANDED (2026-06-22 lane-h resume⁹ cont., commit `2cc5c997`)

**`isCyclic_and_card_dvd_of_odd_two_dim_irreducible`** (S14_MaximalI, sorry-free + axiom-clean,
AxiomsCheck-registered): odd `E` acting **faithfully + irreducibly** on a 2-dim `𝔽_p`-space `V`
with `p ∤ |E|` ⟹ `E` cyclic ∧ `|E| ∣ |V| − 1 = p² − 1`.  Proof = `odd_two_dim_abelian` (BG 2.6(a))
→ `.comm` → RESOLVED comm-Singer lemma.  This is **Case B core of (12.12)**.

🔑 **instance-handling that finally worked** (after the `ρ.asModule`-synthesis quagmire): take
irreducibility as an **explicit** hypothesis `(hirr : Representation.IsIrreducible ρ)` (NOT an
instance — an `[IsIrreducible ρ]` *instance* in scope wedges `Module (𝔽_p[E]) ρ.asModule`
synthesis, confirmed), and put the module on `V` directly via
`letI : Module (𝔽_p[E]) V := Module.compHom V (ρ.asAlgebraHom).toRingHom` (definitionally
`ρ.asModule`'s instance) + `hsmul : of e • x = ρ e x` (via `asAlgebraHom_of`) + `IsSimpleModule`
from `(irreducible_iff_isSimpleModule_asModule ρ).mp hirr`.  Apply comm-Singer with `M := V`
(no `asModuleEquiv` transport needed).  `[Fact p.Prime]` required (for `IsIrreducible`'s `Field`).

## ✅✅ (12.9) centralizer core LANDED (2026-06-22 lane-h resume¹⁰, commits `6afee77c` / `b0a337ef`)

The **§8-independent** group-theoretic heart of the centralizer step of (12.9), in two forms,
both **sorry-free + axiom-clean** (AxiomsCheck-registered):

1. **`exists_ne_one_actionFixedBy_not_le_commutator`** (abstract): a **noncyclic abelian** `A`
   acting **coprimely** on a finite `K` with `[K, K] ≠ K` has `a ≠ 1` with
   `actionFixedBy φ a ⊄ commutator K` (`C_K(a) ⊄ [K, K]`).
2. **`exists_mem_centralizer_inf_not_le_commutator`** (conjugation/ambient — the form (12.9)
   consumes): a noncyclic abelian `A ≤ G` normalizing a coprime `K ≤ G` with `⁅K, K⁆ ≠ K` has
   `x ∈ A^#` with `C_G(x) ⊓ K ⊄ ⁅K, K⁆`.

Proof: BG Prop 1.16(1) (Isaacs 6.21, `nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`)
applied to the **induced action on `K / [K, K]`** ⟹ `K/[K,K] = ⟨C_{K/[K,K]}(a)⟩` is nontrivial
⟹ some `C_{K/[K,K]}(a) ≠ 1`; the witnessing coset **lifts** (Isaacs Cor 3.28,
`coprime_fixedPoints_quotient`) to a `c ∈ C_K(a)` outside `[K, K]`.  The ambient form bridges
`actionFixedBy (normalizerMonoidHom) = C_G(·) ⊓ K` and `(commutator ↥K).map K.subtype = ⁅K, K⁆`
(`map_commutator`).

This **strengthens** the repo's pre-existing weaker conjugation form
`exists_mem_inf_centralizer_ne_bot_of_not_isCyclic` (`S07_Transitivity`, gives only `C_K(x) ≠ 1`)
to the `C_K(x) ⊄ K'` form that (12.9) genuinely needs (`C_{K/K'}(x) ≠ 1`).  Applied with
`A = Ω₁(P₀)` (elem-ab rank 2, noncyclic), `K = M_F` (coprime to `p` since `M_F` is Hall),
`⁅K,K⁆ = K'`, it gives `x ∈ Ω₁(P₀)^#` with `C_K(x) ⊄ K'` — the third conjunct of (12.9).

**Remaining (12.9) assembly** (= `exists_rankTwoWitness`, §8-gated plumbing, NOT genuine new math):
faithful-ize `CounterexampleHypothesis`/`RankTwoWitnessData`, then construct the witness data from
(a) `P₀` rank 2 ← **(8.12.a)** [ABSENT — state faithfully, cite BG §16]; (b) the second maximal
`L` with `P₀ ⊆ L_s` ← **(8.17.a)** (`bgTheoremE_cover_data`) + **(8.11)** (`hall_…`) + Sylow
conjugation [hard plumbing over `BGTheoremECoverData`]; (c) the centralizer conjunct ← **this core**
(needs the `Ω₁(P₀)`-noncyclic + `M_F`-Hall-coprime setup); (d) `N_G(⟨x⟩) ⊆ M`, `C_G(x) ⊄ L` ←
**(8.12.b)** (`typeI_or_typeII_centralizer_unique`).

## ▶ Next steps — full (12.12) `complement_cyclic_order_dvd` (Pf 04.14 L67-74, §8-gated)

The book proof of (12.12): let `P = O_p(H)`, `T = Ω₁(Z(P))` (elem-ab of order `p` or `p²`),
`E` normalizes `T` and (by (12.10)) **acts FPF on `T`**.
- **Case A** (`E` normalizes an order-`p` subgroup of `T`, i.e. faithful on a line): ✅ **core
  landed** (`isCyclic_and_card_dvd_of_faithful_one_dim`, commit `f13d57ca`) — `E ↪ End(line)ˣ ≅
  (ℤ/p)ˣ` ⟹ cyclic, `e ∣ p−1`.
- **Case B** (`|T| = p²`, `E` irreducible on `T`): ✅ **core landed** gives cyclic ∧ `e ∣ p²−1`.
  **`p+1` refinement**: any `A ≤ E` with `|A| ∣ p−1` embeds in `𝔽_pˣ`, so normalizes every line
  of `T`; in particular `⟨x⟩` (`x ∈ T = Ω₁(P_0)`), so `A ⊆ M` (by (12.9)), so `A = 1` (by (12.11)).
  Hence `gcd(e, p−1) = 1`, and with `e ∣ p²−1 = (p−1)(p+1)` ⟹ `e ∣ p+1`.
- **gate**: the `T`/FPF setup + the `A=1` refinement consume **(12.9)/(12.10)/(12.11)**, which are
  the §8-gated counterexample scaffold ((8.12.a) Sylow-of-U rank ≤ 2, (8.13.c1) `L = L_F ⋊ (M∩L)`
  — BG §16 consequences not yet extracted in repo S10) + `CounterexampleHypothesis`/`RankTwoWitnessData`
  faithful-ization.  ⟹ (12.12) as a whole is blocked on that scaffold; the Case B *core* is the
  ungated, reusable part and is done.

Optional ungated fragments (small, reusable, but cannot close (12.12) without the scaffold):
Case A lemma (`E` FPF + normalizes order-`p` line ⟹ `E ↪ (ℤ/p)ˣ`), and "an `𝔽_pˣ`-acting
`A` normalizes every line".

   ### ⚠ Instance-engineering blocker (diagnosed 2026-06-22 — ✅ SUPERSEDED/RESOLVED, see "RESOLVED" block above; kept as a record of the dead ends)
   The clean composition is **blocked** because the Singer lemma requires `[CommGroup C]` but
   BG 2.6(a) yields commutativity as `IsMulCommutative` on a plain `[Group E]`.  Confirmed:
   - `nonempty_singerFieldData` genuinely needs **`[CommGroup C]`** — it uses
     `(MonoidAlgebra.of (ZMod p) C).toHomUnits` (`of c` must be a *unit* ⟹ needs `Group C`)
     **and** a *direct* `CommMonoid C` (for `MonoidAlgebra` to be a `CommRing`).
   - Weakening the file-level `variable` to `[CommMonoid C]` ⟹ `toHomUnits` fails (no Group).
   - Weakening to `[Group C] [IsMulCommutative C]` ⟹ **whnf heartbeat timeout** in
     `nonempty_singerFieldData` (the `CommMonoid` derived via the *scoped* `IsMulCommutative`
     instance explodes during `MonoidAlgebra` `CommRing` / `Ideal.Quotient.field` resolution).
   - In S14, `letI : CommGroup E := { ‹Group E› with mul_comm := … }` shadows `E`'s monoid and
     breaks synthesis of `Module (MonoidAlgebra (ZMod p) E) ρ.asModule` (the `asModule` instance
     is tied to the original `Group E` monoid).
   - **Universe**: the Singer construction forces `C M : Type u` (same universe, since
     `M ≅ K = 𝔽_p[C]/I`); fine for (12.12) since `E, T` are both subtypes of `G`.

   **The `@`-explicit approach was tried (2026-06-22) and ALSO fails.**  Building
   `cgE : CommGroup E := { ‹Group E› with mul_comm := hcomm.comm }` as a term and applying
   `@isCyclic_…_faithful_irreducible p _ E ρ.asModule cgE _ _ _ hirr hfaith'`: TC synthesis
   for the `Module (MonoidAlgebra (ZMod p) E) ρ.asModule` arg (registered for the *ambient*
   `Group E`) will **not unfold the `let cgE`** to match, so both the Module `_` and `hirr`
   (`IsSimpleModule … cgE` vs `… Group E`) mismatch.  The defeq exists but TC does not traverse it.
   ✓ The pieces that DO work (worked out, reusable): `hfaith'` (from `Function.Injective ρ` via
   `ρ.asModuleEquiv_symm_map_rho` + `ρ.asModuleEquiv.symm.injective`; finish with `map_one` then
   `(1 : Module.End …) v` defeq `v`), `hchar` (`CharP (ZMod p) q ⟹ q = p` via `CharP.eq`/`ZMod.charP`,
   contra `¬ p ∣ |E|`), the card step (`Module.card_eq_pow_finrank` + `ZMod.card`), and the
   same-universe binders `{E V : Type u}` (autoBound — no universe error).

   **Real path (next session):** the SingerField-reuse route is a dead end for the
   `IsMulCommutative`-on-`Group` input.  Either (a) **re-derive the order bound natively in the
   `Representation` framework**: for an irreducible faithful `Representation (ZMod p) C V` with
   `[IsMulCommutative C]`, `End_{𝔽_p[C]}(V)` is a finite field (Schur + commutative ⟹ division
   ring is a field), `V` is a 1-dim vector space over it, `C ↪ (End)ˣ` cyclic ⟹ `|C| ∣ |End|−1`;
   no `MonoidAlgebra`/`CommGroup` plumbing.  Or (b) **transport via a `CommGroup` type-synonym**
   `Eᶜ := E` carrying `CommGroup`, move the `Representation`/action across, apply the existing
   Singer lemma there, transport `IsCyclic`/card back ([[lean-type-synonym-fixes-instance-diamond]]).
   Both are multi-session.  See [[lean-coupled-engine-fields-and-beta]].
2. **Faithful-ize** `CounterexampleHypothesis` / `RankTwoWitnessData` (replace opaque `Prop`
   fields with real statements).
3. **State §8 obligations** (8.12.a), (8.13.c1) faithfully in S14 (cite BG §16) and prove
   (12.9) [witness via [BG]1.16] and (12.11) [via (9.1) Wielandt — infra ready].
4. (12.10) and (12.13)–(12.16) are char-heavy (lane-b); (12.7)/(12.17) are the assembly.

## Status of lane-h §-frontier (2026-06-22)

- §9 Wielandt chain (9.1/9.3/9.4/9.6) — **DONE** (group theory, ungated).
- §12 (S14) type-I-Frobenius — upstream frontier, **§8-gated** as above.
- §13 (S15) `|P|=p^q` (`basic_structure.P_order`) — gated on (10.11)/(11.7) (lane-b).
