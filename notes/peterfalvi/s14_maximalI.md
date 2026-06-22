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

## ▶ Next steps (the §12 program for lane-h)

1. **Full FPF rank-≤2 lemma** (extend the above to be directly (12.12)-shaped):
   `E` finite, `|E|` odd, acting faithfully + fixed-point-freely on elem-abelian `V`
   (`|V| ∈ {p, p²}`, `p` odd) ⟹ `E` cyclic, `|E| ∣ p²−1`.  Glue:
   - rank 1 / reducible rank 2: `E ↪ Aut(ℤ/p) ≅ (ℤ/p)ˣ` cyclic, `|E| ∣ p−1`.
   - irreducible rank 2: **`odd_two_dim_abelian`** (BG 2.6(a), S02 ✓; takes a `Representation
     (ZMod p) E V`, returns `Std.Commutative (·*·)`) abelianizes `E`, then the Singer lemma above.

   ### ⚠ Instance-engineering blocker (diagnosed 2026-06-22, 3 confirmed walls)
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
