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
  **⚠ NOT absent (2026-06-23 correction)**: this IS BG **Theorem B(1)**
  `OddOrder.BG.Ch4.S16.theoremB_U_sylow_abelian_rank_le_two`, **proved** in the repo.  (12.9) now
  cites it; the real residual is the `(κ∪σ)ᶜ`-Hall complement `U ⊇ P₀` = **Prop 16.1** (see the
  "(12.9) status" section below).  S10 has (8.12.b) (`typeI_or_typeII_centralizer_unique`).
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

## ✅✅✅ (12.9) honest assembly LANDED (2026-06-23 lane-h resume¹⁰ cont., commits `c99cbe7e` / `cd9d8286`)

The scaffold is **faithful-ized** and **(12.9) `exists_rankTwoWitness` is sorry-free**, honestly
reduced to genuine math + faithful §8 obligations.

**Faithful-ized** (`c99cbe7e`): `CounterexampleHypothesis` (opaque Props → `P0_pGroup`/`P0_sylow`
[`IsPGroup` + `relIndex`], `P0_noncyclic`, `p_dvd_index` `p ∣ [M:M_F]`, `minimal_p` via new `InPi`
predicate) and `RankTwoWitnessData` (`L_type`/`L_hasType` + `P0_le_Ls` `P₀⊆L_s`, `x_mem_omega1`
`x^p=1`, `CKx_not_le_Kprime` `C_K(x)⊄K'`, `centralizer_x_not_le_L`).  (12.11) facts moved out of the
witness to the honest conclusion of `intersection_complement_structure`.  (12.9) conclusion is now
`IsMulCommutative P₀ ∧ rank P₀ = 2 ∧ Nonempty (RankTwoWitnessData)`.

**Genuine, §8-free, axiom-clean** (`cd9d8286`, AxiomsCheck-registered):
`exists_orderP_centralizer_witness` — from the counterexample data (P₀ abelian, coprime to K=M_F,
normalizing K, K not perfect) ∃ order-`p` `x ∈ Ω₁(P₀)^#` with `C_K(x) ⊄ K'`.  Applies the
conjugation centralizer core to P₀ acting on K, then passes to the order-`p` power `x = y^(|y|/p)`
(its centralizer ⊇ `C_K(y)`, so still escapes K').  Uses `IsPGroup.iff_orderOf` + `orderOf_injective`
+ `Commute.pow_left`.

**Faithful §8 obligations** (sorried, citing BG §16 / repo S10 — the residual §8-gate):
- `counterexample_P0_K_structure` ((8.12.a)[ABSENT rank-2]+(8.11)[Hall coprime]): P₀ abelian rank 2,
  coprime to K, normalizing K, K not perfect.
- `exists_second_maximal` ((8.17.a) `bgTheoremE_cover_data` + Sylow conjugation): L, L_type, P₀⊆L_s.
- `centralizer_control_of_CKx` ((8.12.b) `typeI_or_typeII_centralizer_unique`): N_G(⟨x⟩)⊆M, C_G(x)⊄L.

`exists_rankTwoWitness` assembles these into the witness.

**Two of the three obligations discharged** (2026-06-23 lane-h resume¹⁰ cont.², commits
`c23b2134` / `cca59fcc`):
- **`centralizer_control_of_CKx` ((8.12.b)) — sorry-free.** Apply `typeI_or_typeII_centralizer_unique`
  with `U = M`, `X = {x}` ⟹ `C_G(x) ≤ M ∧ IsUniquelyMaximal (C_G(x))`.  Then `N_G(⟨x⟩) ⊆ M`
  (⟨x⟩ proper [`x ∈ M < ⊤`] + nontrivial ⟹ not normal in simple `G` ⟹ `N_G(⟨x⟩) < ⊤` lies in a
  maximal over `C_G(x)` = `M`) and `C_G(x) ⊄ L` (any maximal `L ≠ M` over `C_G(x)` would equal `M`).
  `exists_second_maximal` strengthened to also yield `L ≠ M`.  ⚠ The earlier note "(8.12.b)'s
  `N_G(⟨x⟩)⊆M` exceeds `typeI_or_typeII_centralizer_unique`" was wrong — the unique-maximal property
  + `G` simple suffices.
- **coprime / `P₀ ≤ N_G(K)` / `⁅K,K⁆ ≠ K` discharged inline** in `exists_rankTwoWitness`:
  `(8.11)` (`hall_…`) ⟹ `M_F` Hall ⟹ `p ∤ |M_F|` (`p ∣ [M:M_F] ∣ [G:M_F]`) ⟹ p-group `P₀` coprime
  to `K`; `P₀ ≤ M ≤ N_G(M_F)` (`maxNilpotentNormalHall_le_normalizer`); `K = M_F` nilpotent +
  nontrivial (`TypeFData.H_nontrivial`) ⟹ `commutator ↥K < ⊤` ⟹ not perfect.

**Residual = exactly two honest §8 obligations**:
- **`counterexample_P0_K_structure` ((8.12.a), ABSENT)**: `P₀` abelian of rank 2 (every Sylow of the
  type-`I` complement abelian rank ≤ 2 — a BG §16 consequence not extracted in repo).
- **`exists_second_maximal` ((8.17.a)) — ✅ DISCHARGED** (2026-06-23, commit `c0c11d1b`): the second
  maximal `L ≠ M` with `P₀ ⊆ L_s`.  `p ∈ π(G)` (from `p ∣ [M:M_F] ∣ |M| ∣ |G|`) is covered by some
  `π((reps i)_s)` (`bgTheoremE_cover_data`), giving `L₀` of type `Lt` with `p ∣ |（L₀)_s|`; by (8.11)
  `(L₀)_s` is Hall ⟹ contains a Sylow `p` `Q` (new **`exists_sylow_le_of_hall`**: `v_p(|H|)=v_p(|G|)`
  + `Sylow.ofCard`); `P₀ ≤ Q'`, `Q,Q'` conjugate, so `P₀ ⊆ conj g • (L₀)_s = (conj g • L₀)_s`
  (**`mainSubgroup_pointwise_smul`**).  `L = conj g • L₀` maximal + type `Lt`
  (**`hasPeterfalviType_pointwise_smul`**); `L ≠ M` via type exclusivity (`not_isTypeI_of_isTypeNonI`)
  + coprimality.  Reduces to the cited `bgTheoremE_cover_data` (BG §16) + `hall_…` (8.11).

  **Unblocked by the hub-assigned 5-type conjugation infra (issue 2015, commit `1255e479`)**: extended
  `MaximalSubgroupTypeConj.lean` from F/I to all 5 types — `TypePData.conj`,
  `TypeII/III/IV/VData.conj`, `isType{II..V}_pointwise_smul`, general `hasPeterfalviType_pointwise_smul`,
  `mainSubgroup_pointwise_smul` + helpers (`derivedInG_pointwise_smul`, `secondDerivedInAmbient_…`,
  `isNilpotent_…`, `fitting_map_subtype_…`).  All sorry-free + axiom-clean.

## ✅ lane-h (12.9) status (2026-06-23 resume¹²): residual = (κ∪σ)ᶜ-Hall complement (Prop 16.1), NOT "(8.12.a) absent"

**⚠ STALE CORRECTION**: earlier notes said "(8.12.a) absent from repo".  **(8.12.a) is NOT absent** —
BG **Theorem B(1)** `OddOrder.BG.Ch4.S16.theoremB_U_sylow_abelian_rank_le_two` ("every Sylow of the
type-`I` complement `U` is abelian of rank ≤ 2") is **proved** in the repo (body sorry-free; landed by
lane-f, in S14's import closure via `S10_MinimalSimpleStructure`).

`(12.9) counterexample_P0_K_structure` is now a **gated-endpoint skeleton** (commit `96c793b0`): it
**cites the proven Theorem B(1)** (rank ≤ 2 + abelian) + `two_le_rank_of_noncyclic_pSubgroup`
(2 ≤ rank from `P0_noncyclic`) ⟹ rank = 2.  The substantive math is wired and load-bearing.

**The real residual gate** is now the precise obligation `exists_sigmaKappaCompl_hall_ge_P0`
(sorried): the type-`I` `M` has a `(κ(M) ∪ σ(M))ᶜ`-Hall complement `U ⊇ P₀`.  This is the BG §16 /
**Proposition 16.1** bridge: the type-data complement of `M_F` is `π(M_F)ᶜ`-Hall (ungated, from
`M_F` normal Hall), and Prop 16.1's type-`I` classification (κ=∅, σ=π(M_σ), M_F=M_σ) identifies
`π(M_F)ᶜ` with `(κ∪σ)ᶜ`.  ⟹ **(12.9) auto-closes once lane-f lands Prop 16.1** (their active
frontier) — no further lane-h math needed beyond discharging this Hall-complement existence.

Everything else in (12.9) discharged: (8.12.b) (`centralizer_control_of_CKx`),
coprime/normalize/K-not-perfect (inline), (8.17.a) (`exists_second_maximal`), genuine centralizer
core (`exists_orderP_centralizer_witness`, axiom-clean).

Remaining lane-h frontier: `(12.10)`/`(12.11)`/`(12.13)`–`(12.16)` gated on absent §8
((8.13.c1)/(8.1.b/c)) + char (lane-b); §15 `basic_structure` gated on (10.11)/(11.7) (lane-b).
**lane-h has no ungated closable Lean work** — all residuals are cross-lane (lane-b char / lane-f §16).

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
- **✅ Combined FPF rep-theory core LANDED** (2026-06-23, commit `03b868e5`, sorry-free + axiom-clean):
  **`isCyclic_and_card_dvd_of_fpf_dim_le_two`** — an odd FPF `E` (`p∤|E|`) acting on an `𝔽_p`-space
  `V` of dim 1 or 2 is cyclic with `|E| ∣ |V|−1`.  **Consumes BOTH Case A/B cores**: FPF ⟹ faithful;
  dim 1 / dim-2-reducible (invariant line via `Subrepresentation`) ⟹ Case A; dim-2-irreducible ⟹
  Case B (`|E| ∣ p−1 ∣ p²−1` lift for the reducible case).  This is the **§8-free rep-theory input**
  that the full (12.12) consumes once its `T`/FPF setup lands.
- **✅✅ Conjugation-action bridges LANDED** (2026-06-23 lane-h resume¹¹, commit `9e322459`,
  sorry-free + axiom-clean, AxiomsCheck-registered) — the elem-ab→`Representation` conversion is
  **done**, lifting the dim≤2 core to the form the full (12.12) consumes:
  - **`isCyclic_and_card_dvd_of_fpf_mulDistribMulAction`** (abstract): odd FPF `E` (`p∤|E|`) on an
    elem-ab p-group `M` (`Module (ZMod p) (Additive M)`) of 𝔽_p-dim 1 or 2 ⟹ cyclic, `|E| ∣ |M|−1`.
    Converts `MulDistribMulAction E M` → `Representation` via `Representation.ofDistribMulAction`
    (FPF translated through `Additive.toMul`), applies `isCyclic_and_card_dvd_of_fpf_dim_le_two`.
  - **`isCyclic_and_card_dvd_of_fpf_conj_elemAbelian`** (conjugation): `E ≤ N_G(T)` acting FPF by
    conjugation on elem-ab `T` of order `p` or `p²` (|E| odd, coprime p) ⟹ cyclic, `|E| ∣ p−1 ∨ p²−1`.
    Builds the conjugation `MulDistribMulAction ↥E ↥T` via `compHom` + mathlib's
    `MulDistribMulAction (normalizer ↑T) ↥T`, uses `subgroupCommGroup`/`subgroupZmodModule` to dodge
    the `Additive ↥T` diamond, recovers `finrank∈{1,2}` from `|T|∈{p,p²}` via
    `FiniteField.pow_finrank_eq_natCard` + `Nat.pow_right_injective`.  **This is exactly the form
    the full (12.12) `T`-setup feeds.**
- **✅✅✅ `p+1` refinement rep-theory core LANDED** (2026-07-01 lane-b resume, commit `45f18adc`,
  sorry-free): **`isCyclic_and_card_dvd_add_one_of_two_dim_irreducible_nonscalar`** (S14) — an odd
  `E` (`p∤|E|`) acting faithfully + irreducibly on 2-dim `V` with **no nontrivial element acting as
  an `𝔽_p`-scalar** ⟹ cyclic, `|E| ∣ p+1` (previously Case B core only gave `|E| ∣ p²−1`).  Realizes
  the `p+1` half via the new Singer core **`coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar`**
  (`SingerField.lean`): the realization `μ:E↪Kˣ` meets the prime-subfield units `ν:𝔽_pˣ↪Kˣ` trivially
  (the non-scalar condition) ⟹ `Coprime |E| (p−1)`; combined with `|E| ∣ p²−1 = (p−1)(p+1)` this forces
  `|E| ∣ p+1`.  `..._fpf` (the (9.7)(b) bridge) refactored to a thin wrapper over this core (−50 lines
  dup, signature unchanged, S11 consumer intact).  full build 3890 jobs green, AxiomsCheck OK.
- **gate (remaining)**: only the `T = Ω₁(Z(O_p(H)))` **construction** (`|T|∈{p,p²}` from (12.9)
  rank 2; `E` normalizes & acts FPF on `T` from (12.10) Frobenius) + **discharging the non-scalar
  condition** (the abstract "`A=1`") from the `N_G(⟨x⟩)⊆M` witness structure ((12.9)/(12.11)) —
  these consume **(12.10)/(12.11)** [char/§8-gated, lane-b] and the intricate `O_p/Z/Ω₁` p-group
  structure.  ⚠ Also `complement_cyclic_order_dvd` **as currently stated** takes only `frob`+`ctr`
  (no `RankTwoWitnessData`), so it lacks the witness data (`x`, `N_G(⟨x⟩)⊆M`) needed to establish
  non-scalar-ness for the `p+1` branch — its **statement likely needs the witness added** before it
  can cite the new core.  ⟹ `complement_cyclic_order_dvd` (full disjunction) stays gated; the
  **rep-theory core (incl. the `p+1` half) is the ungated reusable part and is now COMPLETE**.  Wiring
  (12.12) to consume it is "保険 skeleton" over a genuinely-blocked upstream ((12.10)/(12.11)) — defer
  per ft_path_policy until (12.10)/(12.11) land or by hub decision.

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

## 2026-06-28 (lane-b = β 立ち上げ, 新方針 signature contract): §12 char tower の埋め方確定

Owner = **lane-b (β)** (2026-06-28 relane、worktree `odd-order-b`)。過去の「§12 残 sorry は全部
char/§8-gated で手詰まり」評価は**誤り**(= 新方針が根絶する待ち文化)。R(χ) machinery は §6/§8
(certain-type coherence, Round B)に在庫し、§12 (型 I)はその**型 I 再利用**。正面から埋める。

**確定した埋め方**(原文 04.14 精読 + machinery 調査):
- **R(χ) = `S07.OrthonormalCharacterImageFamily hyp.tau φ`**(各 constituent φ)。構成は
  **`S07.dadeOrthonormalCharacterImageFamily`**(S07:5412)を直接 cite。3条件(virtual/
  vanish-at-1/isometry)は `dadeIntegralCharacterMap_mem_ZIrr_of_supported`(S07:5360)/
  `_apply_one_eq_zero`(5381)/`_inner_eq_on_supported_span`(5303)で揃う(全 sorry-free)。
  正準型: `imageSet : Finset (CF G)` + `orthonormal` + `image_eq: τ(φ−φ̄)=Σα`。
  (12.3) = `OrthonormalCharacterImageFamily.Orthogonal`(= 5.2.e、S07:807)。
- **(12.2.a) S(χ) decomp**(χ=Ind_H^L θ の constituents, degree 一定): Clifford
  (`inner_induce_ne_zero_iff_liesOver` Clifford:583 + `restrictionMultiplicity_natCast`)+
  **(8.2.c)**(`I(θ)∩U⊆U₁` inertia, 04.10 (8.2.c))。(8.2.c) は repo 不在 → S14 内 faithful pin。
- **(12.4)/(12.5) ψ⊥R(χ)⟹constant** = `CharacterPsiDecomposition`(InducedCharacter:751)engine
  の型 I 適用。現 (12.4)/(12.5) の free 変数 `R` を (12.2) の genuine R(χ) に bind し直す(現状
  R 抽象ゆえ honest 証明不能)。
- **(12.16) 最終矛盾**: (1.10.a)/(1.10.b) p-進 congruence が **repo 不在** = §12 で新規に要る唯一の
  純 char piece。(7.3)/(7.8) norm bounds は S09 在庫(`chiRho_norm_sq_le` 等)。

**現状 (12.2)-(12.5) scaffold は下流 consumer 0**(S14 内のみ)⟹ faithful 化は安全。
**実装順(上流順)**: (12.2) faithful 化 → (12.3)-(12.5) → (12.13)-(12.15)+(1.10) → (12.16) →
`pi_empty`/`typeI_frobenius`/headline unblock。正本 issue = 0081。
[[scaffold-sorry-free-not-done]] [[feedback-cite-sorried-lemmas-if-signature-correct]]

## 2026-06-28 (lane-b=β loop): (12.2) genuine 完成 + (12.3)-(12.5) 埋め方確定

**(12.2) 完成** (commits 8574ef2a + edf58329, full build 3886 green):
- (12.2.b) `exists_signedFamily_of_constituents` (R(χ) 構成 core): degree-equal constituent family の差分
  を Dade isometry で signed family に ((1.4) `isometry_difference_pair_structure`)。3条件は Dade package
  (`dadeIntegralCharacterMap_{mem_ZIrr_of_supported,apply_one_eq_zero,inner_eq_on_supported_span}`) で
  discharge。**instance 統一の知見** (§12 全体で再利用): helper を `[Fintype G]` binder でなく
  `haveI := hyp.finiteG` + `S12.FiniteInduce` scope (= `Hypothesis.tau` と同 context) にして hyp.tau の
  instance と一致させる。binder の `[Fintype G]` は hyp.finiteG synthesize と非一致で whnf timeout +
  instance desync。
- (12.2) carrier `CharacterDecompositionData` genuine 化 (constituents/decomp/equal_degree/not_real/
  supported)。(12.2.a) `character_decomposition_and_dade_domain` genuine assembly (sorry-free): §8 型 F
  char fact を obligation **`typeI_induced_char_constituents`** (genuine statement, body=§8 型 F Clifford:
  (8.2.c) inertia + (1.7.c)/(1.5.a)/(1.2)) に isolate。

**(12.3)-(12.5) 埋め方確定 (次イテレーション実装)**:
- ⚠ **現 (12.4)/(12.5) statement は `R` free で unsound** (R=∅ で horth trivial、結論 ψ constant は ψ
  任意で偽; (12.3) も R1=R2=∅ で vacuous)。**R を genuine R(χ) に bind 必須**。
- **R(χ) = ∪_{φ∈constituents} R₁(φ)**。R₁(φ) = `exists_signedFamily_of_constituents` を family=![φ, φ̄]
  (Fin 2) に適用した signed family (imageSet = {sign·μ₁, −sign·μ₀})。φ̄=conj (`Sset_closedUnderConjugate`
  の `(θ:CF).conj` + `θ.isIrreducible.conj` パターン)。hyp discharge: hinj←not_real (φ≠φ̄)、hdeg←conj
  次数保存、hsupp←supported。
- **実装**: CharacterDecompositionData に `Rfamily : (φ∈constituents)→OrthonormalCharacterImageFamily
  hyp.tau φ` field 追加 (obligation で供給) → R(χ) derive。(12.3)-(12.5) を R(χ) consume に faithful 化。
- **(12.4)/(12.5) 証明 core = `CharacterPsiDecomposition`** (S07_Coherence:1110, ψ⊥R ⟹ Res_L ψ 分解)。
  S08 certain-type で多用、型 I 適用要確認。+ §8 ((8.12.c) A(L)−H# TI)、§1 ((1.4))、[Is] 6.2/7.7。
- **(12.3)** = (8.18.c) Ã disjoint + (5.9) + Supp((φ−φ̄)^τ)⊆Ã(L) disjoint で R(χ₁)⊥R(χ₂)。

## 2026-06-29 (lane-b=β loop cont.): (12.2)-(12.5) carrier 層 genuine 完成

**(12.2.b) R(χ) carrier 完成** (commits c80bfb92/a8298a69/7b13b1f3/364589f7):
- `conjConstituent` (φ̄=⟨(φ:CF).conj, isIrreducible.conj⟩) + 4性質 (coe / support_conjConstituent
  [star_eq_zero] / conjConstituent_apply_one [degree=irreducibleCharacter_apply_one_eq_pos_natCast +
  star_natCast] / ne_conjConstituent [¬IsReal⟹φ≠φ̄])。**`[Finite ↥L]` instance 必須** (isIrreducible.conj 用)。
- `signedFamily_exists` (R₁(φ) derive 本体): exists_signedFamily_of_constituents を family=![φ,φ̄]
  (Fin 2) に適用、3 hyp を conjConstituent lemma で discharge (fin_cases + show で coe 正規化)。
- `signedFamily` (choose) + `Rset` = {α|∃φ∈constituents,∃i, α=(signedFamily data hφ).μ i} = R(χ)。

**(12.3)-(12.5) faithful 化完成** (commits a0c011d3/5d4ae345):
- (12.4)/(12.5): R free (unsound) → `data : ∀χ∈Sset, CharacterDecompositionData hyp χ` 引数 +
  horth=ψ⊥`(Rset (data χ hχ))`。(12.3): CrossOrthogonalityData 削除 → `∀α∈Rset data1,∀β∈Rset data2,⟨α,β⟩=0`。
- instance: `[Fintype G][Invertible (Nat.card G/↥L:ℂ)]`、L を binder 先頭 (↥L 順序)、`Rset` は explicit
  (top-level、dot notation 不可)。

**残 = (12.3)-(12.5) 証明本体** (次イテレーション、§12 char obligation):
- (12.4)/(12.5) = `CharacterPsiDecomposition` (S07:1110) 型 I 適用 + §8 ((8.12.c) TI) + §1 ((1.4)) +
  [Is] 6.2/7.7。**engine 構造 (2026-06-29 確認)**: CharacterPsiDecomposition は **単一 χ** の
  `imageFamily : OrthonormalCharacterImageFamily τ χ` + smart ctor (`ofProjection` S07:1160) が
  **`(χ−ψ)^τ₁∈ZIrr G`** 単一入力から X/Y/coeff を computed (R(χ) への直交射影)。⟹ (12.4)/(12.5) は
  **各 constituent φ** で CharacterPsiDecomposition(φ,ψ) 構成 (imageFamily=R₁(φ)=signedFamily の
  OrthonormalCharacterImageFamily 化が要、入力 (φ−ψ)^τ₁∈ZIrr) → ψ⊥R(χ) で各 X=0 → Res_H ψ が
  θ_φ-成分を持たない → ψ は L−H で γ (H⊆Ker) のみ → xH/H−H' constant。§12-specific = φ-family 集約。
  **次の壁**: R₁(φ) は現状 SignedIrreducibleDifferenceFamily、engine は OrthonormalCharacterImageFamily
  要 (signed→orthonormal 変換 helper を S14 に要実装)。
- (12.3) = (8.18.c) Ã disjoint + (5.9) + Supp disjoint + 共役論法。§8 cross fact は β 範囲外 (pin)。
- その後 (12.6) sibleyTarget / (12.10)-(12.15) / (12.16) 最終矛盾 (+(1.10) congruence)。

## 2026-06-29 (lane-b=β loop²): R₁(φ) orthonormal 化 + (12.3) genuine 証明完了

**(12.2.b) 壁解消 — R₁(φ) を genuine OrthonormalCharacterImageFamily 化** (commit 278384dc):
- 「signed→orthonormal 変換が次の壁」評価は**回避不要**だった。`S07.dadeOrthonormalCharacterImageFamilyOfDiff`
  (S07:5497、差 φ̄−φ のみ supported を要求、constituent は φ(1)≠0 で個別 unsupported ゆえ正にこれ)が
  τ=hyp.tau に直接 orthonormal family を構成。教科書定義「R₁(φ)=ℤ[Irr G] の濃度 2 orthonormal 部分集合」に
  忠実。signed-family scaffold (exists_signedFamily_of_constituents / conjConstituent+補題 / signedFamily*)
  は subsume されたため除去。`R1` (orthonormal) + `R1_diffsupp` (φ̄−φ⊆A(L)) + `Rset`=⋃R₁(φ).imageSet。
- instance: return type に `haveI := hyp.finiteG; OrthonormalCharacterImageFamily hyp.tau φ` + body も
  同 haveI + S12.FiniteInduce scope ⟹ hyp.tau の instance と完全一致 (binder [Fintype G] は使わない)。

**(12.3) genuine 証明完了** (commit eb5eda20、S07+S14):
- **S07 cross-domain (4.1) インフラ** (再利用可能、sorry-free):
  - `inner_eq_zero_of_signedDifference_inner_zero_of_mem`: 既存 `orthogonal_of_signedDifference_inner_eq_zero`
    を**異なる定義域 L,L' (τ,τ')** に一般化 (証明は元々 τ 非依存)。同域版は委譲 wrapper。
  - `dadeCharacterDifferenceImageOfDiff`: `dadeOrthonormalCharacterImageFamilyOfDiff` から CDI producer を
    factor out (orthonormal 版は `.toOrthonormalImage` wrapper)。R₁(φ) の underlying {μ,ν,ε} 露出。
  - `toOrthonormalImage_inner_eq_zero_across`: 上記を符号付き member {ε·μ,−ε·ν} に持ち上げ (Rset の形)。
- **S14**: `R1cdi` (R₁(φ) の CDI 露出)、`R1 := (R1cdi …).toOrthonormalImage`。`nonconjugate_typeI_R_orthogonal`
  (12.3) を genuine 証明: member→R₁(φ)→cross-L (4.1)→⟨α,β⟩=0 を signed diff 直交に帰着
  (`image_eq_signedDifference`)。幾何学入力 = `nonconjugate_diffImage_inner_zero` (S14:338) に faithful pin
  = (8.18.c) thickened support 不交差 (S10.support_mutual_exclusion、§10=lane-d/f territory)。

**残 frontier = (12.4)/(12.5) 証明本体** (次の上流項目、engine は ready):
- `R1` が今や engine `CharacterPsiDecomposition.ofProjection` (S07:1185) の `imageFamily` 引数に直接適合
  (= OrthonormalCharacterImageFamily)。signed→orthonormal の壁は無い。
- (12.4) `orthogonal_character_constant_on_coset` (S14:382): χ=Ind_H^L θ, φ₁,φ₂∈S(χ) で Supp(φ₁−φ₂)⊆
  A(L)−H#、(8.12.c) で TI⟹(φ₁−φ₂)^τ=Ind (Is 7.7)、(1.4) coherence⟹(φ₁−φ₂)^τ∈ℤ[R(χ)]⟹(Res_H ψ,φ₁−φ₂)=0
  (ψ⊥R(χ))。Res_L ψ=β+γ (β∈ℂ[S], γ は H⊆Ker)、S は L−H で消える⟹ψ(xh)=γ(x)。
  pin 候補: [Is] 6.2 (Res_H Ind=共役和)、[Is] 7.7 (TI 上で τ=Ind)、(8.12.c) (A(L)−H# TI)。
- (12.5) `rho_constant_on_H_minus_Hprime` (S14:395): θ₁,θ₂∈Irr H 同次数、χᵢ=Ind θᵢ、(5.7) coherence、
  (5.5) で (χ₁−χ₂)^τ∈ℤ[R(χ₁)∪R(χ₂)]⟹(Res_H ψ^ρ,θ₁−θ₂)=0。(1.7.b)+Ind_{H'}^H λ が H−H' で消える。

## 2026-06-29 (lane-b=β loop⁴): (12.4) 完成 (genuine、3 pin modulo) + 残 frontier 整理

**(12.4) `orthogonal_character_constant_on_coset` genuine 証明完了** (commits c83e47f2 + 56e6bba6):
- Fourier 展開 (sum_inner_irreducibleCharacter_smul) で Res_L ψ=γ+β に分割 (InHKernel 述語)。
  γ (H⊆ker) coset-const = apply_mul_eq_of_mem_characterKernel (既存)。β (H⊄ker) L−H 消失。
- **pin (c) discharge 済**: β-vanishing を genuine 化。off-kernel sum を S(χ) partition で regroup
  (Finset.sum_biUnion + Sset_coeff_equal 係数一定 + decomp + Sset_vanishes_off_H)。
- 補助 genuine: `Sset_vanishes_off_H` (S 元が L−H で 0)、`Sset_coeff_equal` (ψ⊥R(χ)⟹S(χ) 係数一定、
  Frobenius inner_induce_eq_inner_restrict + pin a,b)、`classFunction_sum_apply`。

**残 (12.4) pin = 3 純 cross-section faithful obligation**:
- (a) `constituent_diff_tau_mem_span`: (φ₁−φ₂)^τ∈ℤ[R(χ)] ((1.4) global coherence)。discharge には
  n-ary (1.4) 再導入 + per-φ R₁(φ) との reconciliation 要 (ℤ-span は一致するが μ 対応付けが involved)。
- (b) `constituent_diff_tau_eq_induce`: (φ₁−φ₂)^τ=Ind_L^G(φ₁−φ₂) ([Is]7.7 τ=Ind on TI)。repo の
  S05 `tau_eq_induce` は TI-cyclic 用で型 I 不適用。Dade-on-TI 一般化要。
- (c') `exists_offKernel_constituent_partition`: {φ:H⊄ker}=⊔S(χ) ([Is]6.2 capturing + uniqueness)。
  Clifford theory (CliffordSingleOrbit 等) 部分在庫 → 比較的 tractable か。

**(12.5) は ρ-blocked (要判断)**: repo statement `psi h=psi 1` は **unfaithful** (ρ 無 + =psi 1 が
constant-on-H−H' でない)。book は「ψ^ρ が H−H' で constant」。ρ (Hypothesis 7.1, A=A(L)) は repo 未
形式化 (S09 chiRho/FamilyHypothesis71 は family 特化、型 I A(L) 一般 ρ 不在)。faithful 化には §7 ρ
machinery 構築 (大、§7 prerequisite) 要。

## 2026-06-29 (lane-b=β loop⁵-¹⁰): pin (c') 完全 discharge — [Is]6.2 partition genuine

**pin (c') `exists_offKernel_constituent_partition` 完全 discharge** (commits 99db2c93 → d7fe3fc7 →
8bd87b1c → e817e3ee → 6bf6f93b)。{φ:H⊄ker}=⊔S(χ) を bottom-up で全 genuine 化:
- `constituents_not_inHKernel` (⊇): constituent は off-kernel (Frobenius + decomp + characterKernel)。
- `not_inHKernel_imp_mem_constituents` (⊆): off-kernel φ は capturing
  (`exists_constituent_not_subset_characterKernel` [Is]6.5 + Frobenius)。
- `not_inHKernel_iff` (両方向 ↔)。
- `constituents_eq_of_mem` (disjointness): Clifford single-orbit
  `restrictionConstituentsSingleOrbit_of_isIrreducible.exists_conj` + `induce_conjBy_eq` (Pf 1.5.a)。
- pin 本体: parts=image(cap)、biUnion 等式 + PairwiseDisjoint の Finset 組立 (content lemma を pin
  前に reorder)。

**(12.4) は残 pin (a)(b) modulo で genuine closed**。pin (c) regroup + (c') partition 両方 genuine。

**残 §12 char frontier (全て deeper cross-section/§7/§8 machinery)**:
- pin (a) `constituent_diff_tau_mem_span` (S14:400): (φ₁−φ₂)^τ∈ℤ[R(χ)] ((1.4) global coherence +
  per-φ R₁(φ) reconciliation)。**concrete 3-piece plan (2026-06-29 確認)**:
  1. **n-ary (1.4)**: `isometry_difference_pair_structure` (IsometryDifferencePair:730) を constituent
     family に適用 ⟹ global SignedIrreducibleDifferenceFamily で τ(φᵢ−φ₀)=ε(μᵢ−μ₀) ⟹
     τ(φ₁−φ₂)=ε(μ_{φ₁}−μ_{φ₂})。(削除した exists_signedFamily_of_constituents の再導入)。
  2. **difference-uniqueness reconciliation**: global μ_{φ₁} は τ(φ₁−φ̄₁) の既約成分。R1cdi の
     image_eq: τ(φ₁−φ̄₁)=ε_cdi(μ_cdi−ν_cdi)。両者 = 同じ τ(φ₁−φ̄₁) ⟹ ε(μ_{φ₁}−μ_{φ̄₁})=
     ε_cdi(μ_cdi−ν_cdi) ⟹ `linearIndependent_irreducibleCharacter` (CharacterCount:86) で
     {μ_{φ₁},μ_{φ̄₁}}={μ_cdi,ν_cdi} ⟹ μ_{φ₁}∈{μ_cdi,ν_cdi} ⟹ ±(R1cdi.toOrthonormalImage.imageSet member)
     ∈ ℤ[Rset]。要 difference-uniqueness lemma (s(α−β)=s'(γ−δ), 既約 distinct ⟹ pair 一致、
     線形独立から、~30 行、新規)。
  3. **span assembly**: τ(φ₁−φ₂)=ε(μ_{φ₁}−μ_{φ₂})、μ_{φᵢ}∈ℤ[Rset] ⟹ ∈ℤ[Rset]。
  深い multi-iteration proof (~100+ 行)。次イテレーションで piece 1 から bottom-up。
  **alt path (conj-difference、より clean だが要 Dade-conj-commute)**: (φ₁−φ₂)−(φ̄₁−φ̄₂)=
  (φ₁−φ̄₁)−(φ₂−φ̄₂) ⟹ τ(φ₁−φ₂)−τ(φ₁−φ₂).conj = τ(φ₁−φ̄₁)−τ(φ₂−φ̄₂)=∑R₁(φ₁)−∑R₁(φ₂)∈ℤ[Rset]
  (per-φ image_eq のみ、global (1.4)/uniqueness 不要)。**但し** τ(g.conj)=(τ g).conj が要
  (Dade map の複素共役 commute) — supported g では dadeMap = genuine だが、repo に
  complex-conj-commute lemma 不在 (group-conj `induce_map_conj` のみ)。要新規証明 (Dade
  内部、alphaB conj 挙動から、深い)。⟹ どちらの path も deep prerequisite 要
  (uniqueness via linearIndep / Dade-conj-commute)。**difference-uniqueness lemma**
  (s(a−b)=t(c−d), 既約 distinct ⟹ {a,b}={c,d}) は inner-product 経由で証明可 (各 x で
  s([a=x]−[b=x])=t([c=x]−[d=x])、x=a,b,c,d で case 分け、~50 行) = global path piece 2。

## 2026-06-29 (lane-b=β loop¹¹, 再開): pin (a) 両 path の deep prerequisite 確認

pin (a) は (1) global-(1.4)+difference-uniqueness か (2) conj-difference+Dade-conj-commute。
両者とも deep prerequisite (uniqueness lemma ~50 行 / Dade complex-conj commute 新規)。
§12 char frontier は genuine に deep cross-section/Dade machinery 段階。(12.2.b)/(12.3)/(12.4)
は pin (a)(b) + §8/§10/§7 obligation modulo で honest closed、pin (c)(c') 完全 discharge 済。
次: difference-uniqueness lemma (inner-product 経由、tractable) を piece 2 として bottom-up、
or pin (b)/(12.2.a)/§7 ρ の machinery 評価。
- pin (b) `constituent_diff_tau_eq_induce` (S14:413): (φ₁−φ₂)^τ=Ind_L^G ([Is]7.7 τ=Ind on TI、Dade
  machinery; S05 tau_eq_induce は TI-cyclic 用で型 I 不適用)。
- (12.2.a) `typeI_induced_char_constituents` (S14:235): §8 型 F Clifford ((8.2.c) inertia + (1.7.c))。
- (12.3) (8.18.c) `nonconjugate_diffImage_inner_zero` (S14:338): §10 support 不交差 (lane-d/f)。
- (12.5) ρ-blocked (上記)。

## 2026-06-29 (lane-b=β loop³): Sset_vanishes_off_H + (12.4) 精密 reduction 設計

**`Sset_vanishes_off_H` 完成** (commit 66aac2b5): χ=Ind_H^L θ∈S は H=L_F normal (Fitting,
`OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal`) ゆえ `induce_eq_zero_of_not_mem_normal`
で L−H で 0。(12.4)/(12.5) endgame の β∈ℂ[S] 消失 step。両者 consume。

**(12.4) 精密 reduction (次イテレーション実装) — 3 faithful pin + genuine 組立**:
- **adjunction `⟨ψ,τf⟩_G = ⟨Res_L ψ,f⟩_L`** (f=φ₁−φ₂, A(L)−H# supported) は **[Is]7.7 (τ=Ind_L^G on
  TI-subset) + Frobenius reciprocity** に分解。後者は repo 在庫 `inner_induce_eq_inner_restrict`
  (InducedCharacter:531)。⟹ pin は τ=Ind 部分のみ。
- **pin (a)** `τ(φ₁−φ₂)∈zSpan R(χ)` (coherence, (1.4)/{φ₁,φ₂,φ̄₁,φ̄₂} coherent) ⟹ ψ⊥R(χ) で ⟨ψ,τ(φ₁−φ₂)⟩=0。
- **pin (b)** `τ(φ₁−φ₂)=Ind_L^G(φ₁−φ₂)` ([Is]7.7 + (8.12.c) A(L)−H# TI、φ₁−φ₂ は (8.12.a) [Is]6.2 で
  A(L)−H# supported) ⟹ Frobenius で ⟨ψ,τ(φ₁−φ₂)⟩=⟨Res_L ψ,φ₁−φ₂⟩。(a)(b) 合わせ ⟨Res_L ψ,φ₁−φ₂⟩=0
  = S(χ) 内 constituent で Res_L ψ 係数一定 ⟹ ∪S(χ)-part = β∈ℂ[S]。
- **pin (c)** capturing: H⊄ker φ ⟹ φ∈S(χ) ([Is]6.2/Clifford) ⟹ γ=残り は H⊆ker。
- **genuine 組立**: 上記で Res_L ψ=β+γ、β は L−H で 0 (`Sset_vanishes_off_H` ✓)、γ は coset-const
  (H⊆ker character ⟹ φ(xh)=φ(x)、要 character-kernel coset-const lemma) ⟹ ψ(xh)=γ(x)=ψ(x)。
  regrouping は character completeness (`CharacterCompleteness`) + 係数抽出。

## 2026-06-29 (lane-b=β loop¹²): pin (a) piece 2 = difference-uniqueness lemma 完成 + 残 piece の具体 recipe

**difference-uniqueness lemma 完成** (commit ef060c7d、sorry-free + axiom-clean、AxiomsCheck 登録):
`irreducibleCharacter_signed_difference_uniqueness` (S14:407 付近、`[Finite G]`):
`s•(a−b)=t•(c−d)` (a≠b, c≠d, s≠0 ∈ ℂ) ⟹ `(a=c∧b=d∧s=t) ∨ (a=d∧b=c∧s=−t)`。
証明 = 既約 a/b と左 inner で pairing (`ClassFunction.inner` 左線形) + 直交正規
`irreducibleCharacter_inner_eq_ite` で Kronecker delta 化 ⟹ `s=t·([c=a]−[d=a])` /
`−s=t·([c=b]−[d=b])`、s≠0 で 2 orientation 場合分け。**loop⁵-¹⁰/¹¹ が「tractable piece 2」と
判定したもの、回避せず実装**。

**pin (a) `constituent_diff_tau_mem_span` 残 piece の具体 recipe (調査確定、次イテレーション実装)**:
route = **global n-ary (1.4) signed family + reconciliation** (conj-difference path は Dade-conj-commute
新規ゆえ不採用)。**injectivity 懸念は解消** — family を Finset で取れば distinct 自動。

- **piece 1 (global family)**: `isometry_difference_pair_structure` (IsometryDifferencePair:730) を
  family T = `constituents ∪ constituents.image conj` (Finset、φ̄ も含む全 distinct 既約) に適用。
  **template = `S07_CoherenceConstantDegree.coherent_of_constant_degree:527-540`** (`hSfin.toFinset.equivFin`
  で Finset→`Fin n` 列挙 + injective + range=T)。要件:
  - n≥2: φ≠φ̄ (non-real) ゆえ |T|≥2。
  - equal degree: constituents 等次数 (`data.equal_degree`) + φ̄(1)=φ(1) (degree real)。
  - 3 Dade hyp (`IsometryDifferenceImagesAreVirtual`/`...VanishAtOne`/isometry `h_isom`): 全て差
    χᵢ−χ₀ が A(L)-supported から従う。constituents⊆A(L)∪{1} (`data.supported`)、φ̄ 同、等次数で {1}
    相殺 ⟹ A(L)-supported。供給 = `S07.dadeIntegralCharacterMap_{mem_ZIrr_of_supported(:5360),`
    `apply_one_eq_zero(:5381),inner_eq_on_supported_span(:5303)}` (R1cdi が単一 pair で使うのと同じ)。
  - 出力: `data : SignedIrreducibleDifferenceFamily G n` + ∀i, `τ(χᵢ−χ₀)=ε•(μᵢ−μ₀)` (global sign ε,
    global μ:Fin n→Irr G)。⟹ `τ(φ₁−φ₂)=ε(μ_{φ₁}−μ_{φ₂})`、`τ(φ−φ̄)=ε(μ_φ−μ_{φ̄})`。
- **piece 2 (reconciliation, lemma 済)**: 各 constituent φ で R1cdi (`CharacterDifferenceImage`,
  S07_Coherence:395) の `image_eq`: `τ(φ−φ̄)=sign_φ•(mu_φ−nu_φ)` (S07_Coherence:402、χ.conj=φ̄)。
  global と等置 `ε(μ_φ−μ_{φ̄})=sign_φ(mu_φ−nu_φ)` → **`irreducibleCharacter_signed_difference_uniqueness`**
  (μ_φ≠μ_{φ̄}: μ inj + φ≠φ̄; mu_φ≠nu_φ: `.distinct`; ε≠0) ⟹ {μ_φ,μ_{φ̄}}={mu_φ,nu_φ}
  ⟹ μ_φ∈{mu_φ,nu_φ}=`(R1cdi).imageSet`。
- **piece 3 (span assembly)**: mu_φ,nu_φ は `(R1 data hφ).imageSet`=Rset member の ± (orthonormal 化
  `toOrthonormalImage`)。⟹ μ_φ∈span ℤ Rset。∴ `τ(φ₁−φ₂)=ε(μ_{φ₁}−μ_{φ₂})∈span ℤ Rset`。
  ⚠ `toOrthonormalImage.imageSet` vs `R1cdi.imageSet`={mu,nu} の符号関係を 1 つ確認要
  (mu_φ が Rset member の ±1 倍であること)。

**実装順**: piece 1 を sub-lemma 群に分解 (1a=Finset family+equal degree+supportedness、1b=3 Dade hyp、
1c=(1.4) 適用) → piece 2 reconciliation lemma (uniqueness 適用) → piece 3 span。各 committable。
pin (b) (τ=Ind on TI) と (12.5) ρ は別 (deeper Dade/§7)。
[[scaffold-sorry-free-not-done]] [[feedback-no-avoiding-hard-parts]] [[feedback-cite-sorried-lemmas-if-signature-correct]]

**piece 1 の正確な実装 template (loop¹² 末、調査確定)**:
- 列挙: `coherent_of_constant_degree:527-540` (`hSfin.toFinset.equivFin.symm` で Finset→`Fin n`、
  injective/range=T/n≥2)。
- 3 Dade hyp 放出: `dadeOrthonormalCharacterImageFamily:5499-5517` が **Fin 2 で完全な template**
  (hvirtual=`dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp.dadeData.dade hyp.hconj (hdiff_supp i)
  (Submodule.sub_mem .. mem_ZIrr)` / hzero=`..apply_one_eq_zero` / hisom=`..inner_eq_on_supported_span
  .. hSsupp (hdiff_zspan i)(hdiff_zspan j)`)。これを **Fin 2 → Fin n に一般化**(fam=T 列挙、
  hSsupp/hdiff_supp/hdiff_zspan を T 全体に)。
- (1.4) 適用: `isometry_difference_pair_structure:730` (characterDifferenceImageOfIsometry でなく直接)
  → `SignedIrreducibleDifferenceFamily G n` + `∀i, isometryDifferenceImage hyp.tau fam i = sdf.signedDifference i`。
- 補助: φ̄ as Irr = `IrreducibleCharacter.conjPerm ↥L φ` (BrauerPermutationUnconditional:152、coe=`.conj`)。
  `hyp.tau` は `IntegralCharacterMap` (S14:95、=`dadeIntegralCharacterMap hyp.dadeData.dade ..`)、
  (1.4) の `τ:CF→ₗ[ℤ]CF` 引数には IntegralCharacterMap の linear-map coe を渡す
  (`dadeOrthonormalCharacterImageFamily` が `set τ := dadeIntegralCharacterMap ..` で直接渡している)。
- pin (a) は**単一 coherent proof** (~150-200 行、piece 1+2+3 一体) が自然単位。global family は
  existential 中間ゆえ sorry-free 分割が難しい。次イテレーションで一気に書く。

## 2026-06-29 (lane-b=β loop¹³): pin (a) `constituent_diff_tau_mem_span` 完全証明 ✅✅

**pin (a) sorry-free 化完了** (commit 4eecce9c、3 lemma 全 axiom-clean、full build 3849 / AxiomsCheck
3874 green)。loop¹²の recipe を実装:
- `R1cdi_muNu_mem_span_Rset` (piece 3): R₁(φ).imageSet={ε·μ,−ε·ν}⊆R(χ)、ε=±1 ⟹ μ_φ,ν_φ∈span ℤ R(χ)。
- `exists_uniform_image_of_constituents` (piece 1): 共役閉 T=S(χ)∪S(χ)‾ の global (1.4) coherence
  (`isometry_difference_pair_structure` を定次数 family に適用、3 Dade hyp は A(L)-supported 差から
  `dadeIntegralCharacterMap_{mem_ZIrr_of_supported,apply_one_eq_zero,inner_eq_on_supported_span}`)。
  一様符号 ε + 単射 μ:T↪Irr G、τ(α−β)=ε(μα−μβ)。**Finset 列挙で injectivity 自動** (懸念解消)。
- pin (a): global ε(μφ−μφ̄) と per-φ R₁(φ) の ε_φ(μ_φ−ν_φ) を difference-uniqueness で照合。
- **実装知見**: 文の Finset image/union は `open scoped Classical` 要 (DecidableEq)。
  μ の dite は `simp only [dif_pos h]` で beta+解決 (`rw [dif_pos]` は lambda 未適用で pattern 不一致)。
  ℤ-smul→ℂ-smul は `Int.cast_smul_eq_zsmul`。`IntegralCharacterMap=CF→ₗ[ℤ]CF` ゆえ hyp.tau 直接渡せる。

**残 (12.4) gate = pin (b) `constituent_diff_tau_eq_induce`** (τ(φ₁−φ₂)=Ind_L^G(φ₁−φ₂))。
これが埋まれば `Sset_coeff_equal` → (12.4) `orthogonal_character_constant_on_coset` が unblock。
次イテレーション = pin (b) scope ([Is]7.7 τ=Ind on TI; Dade map は supported 上で induce か要確認、
`dadeIntegralCharacterMap_apply_of_support` + Dade map=induce-on-TI)。

**pin (b) `constituent_diff_tau_eq_induce` scoping (loop¹³ 末、次イテレーション)**:
τ(φ₁−φ₂)=Ind_L^G(φ₁−φ₂)。template = `TICyclicHypothesis.tau_eq_induce` (S05_SignedTripleGrid:288)
= `IsDadeMap.unique τ.isDadeMap (isDadeMap_inducedDadeMap)`。2 piece 要:
1. **induce が Dade map (型 I)**: `isDadeMap_inducedDadeMap` (S05:254) は TICyclicHypothesis 専用、
   依存 = `induce_apply_eq_self_of_mem_V` (value-half) + `dadeSupport_eq_conjugatesOfSet_of_forall_H_eq_bot`
   (要 **∀a, H(a)=⊥** = trivial Dade stabilizer)。型 I Dade (`S10.dadeSupportHypotheses_typeI`) が
   ∀a H(a)=⊥ を満たすか要確認 (満たせば inducedDadeMap 構成を DadeHypothesis 一般に generalize して
   IsDadeMap.unique で τ=induce)。⚠ 型 I 全 A(L) で H(a)=⊥ は怪しい (H# 除外がある = (8.12.c))。
   ⟹ TI 部分 (A(L)−H#) でのみ τ=induce の可能性 → supported-restriction 版が要る。
2. **Supp(φ₁−φ₂)⊆A(L)−H#**: [Is]6.2 (Res_H φ=共役和) + 型 F constituent (cross-lane §8、(8.12.a))。
   φᵢ は A(L)∪{1} supported (data.supported)、差で {1} 相殺だが H# 除外は別途。
深い Dade machinery + §8 cross-lane。pin (a) と違い「単一 coherent proof」では済まない可能性大。

## 2026-06-29 (lane-b=β loop¹⁴): pin (b) feasible path 完全マップ (Explore + Dade machinery 調査)

**重要確定: 型 I Dade map は globally induction でない**。H(a)=supportKernel=L_F⊓C_G(a)
(a∈escapingCentralizerSet=`C_G(a)⊄M` のとき)、else ⊥。⟹ **τ=Ind は trivial-H 部分
A₁={a∈A(L):C_G(a)≤M}=A(L)−H# 上のみ**。一般「τ=Ind on trivial-H support」lemma は repo 不在
(TICyclic 専用)。`of_isTISubset` (S04:267) は TI subset→trivial-H Hypothesis 構成するが
「その dadeMap=induce」lemma も一般 TI-induction-self-value も無し。

**pin (b) の feasible 4-step plan (全 in-lane Dade、§8 は support fact のみ)**:
1. **一般 TI-induction self-value** `induce_apply_eq_self_of_mem_tiSubset`: TI subset A
   (L⊆N(A)、A⊆L、TI) + α が A-supported、a∈A ⟹ `Ind_L^G α (a) = α(a)`。
   **template = TICyclic `induce_apply_eq_self_of_mem_V`/`induceTerm_eq_of_mem_V`
   (S05_SignedTripleGrid:199-243)** を一般 TI subset に generalize (V/W/W_normalizes_V/V_subset_W/
   V_ti を explicit hyp 化、of_isTISubset:267 の hyp 形をミラー)。~40-60 行。
2. **一般 induce-is-Dade-map** (trivial-H hyp): `isDadeMap_inducedDadeMap` (S05:254-275) を
   of_isTISubset 仮説に generalize (map_eq_of_isConj_hCoset は H=⊥⟹h=1⟹induce self-value、
   map_eq_zero は `induce_eq_zero_of_not_conjugatesIntoSet`)。step 1 consume。
3. **restriction assembly**: 型 I hyp を A₁=trivial-H 部分に `Hypothesis.restrict` (S04:329)。
   restrict_H (S04:345) で A₁ 上 H=⊥。`Hypothesis.dadeMap_restrict` (S04:3641) で
   global dadeMap|A₁-supported = restricted dadeMap = induce (step2 + IsDadeMap.unique S04:3442)。
   ⟹ A₁-supported f で `hyp.tau f = induce L f`。
4. **§8 support fact** (cross-lane、cite obligation): `Supp(φ₁−φ₂)⊆A₁` ([Is]6.2 + (8.12.a)、
   constituent が escaping 部分で消える)。data.supported は A(L)∪{1} までしか言わない。

**次イテレーション = step 1 (一般 TI-induction self-value) を build** (foundational + reusable、
TICyclic proof mirror)。pin (b) は pin (a) と違い deep multi-iteration Dade 開発 (4 lemma)。
正本ノート = 本節 + issue 0081。[[feedback-no-avoiding-hard-parts]]

**loop¹⁴ 続き: step 1 DONE** (commit 6dbdf835、`induce_apply_eq_self_of_mem_tiSubset`、axiom-clean、
full build 3874 green)。次 = **step 2** (一般 induce-is-Dade-map for TI/trivial-H hyp、
`isDadeMap_inducedDadeMap` S05:254-275 を of_isTISubset 仮説に generalize、step 1 を value-half に consume)。

## 2026-06-29 (lane-b=β loop¹⁵): pin (b) steps 1+2+3 完成 — 一般 Dade machinery DONE

**steps 1+2+3 全 axiom-clean、committed** (6dbdf835 step1 / 0125ce2a steps2+3):
- step 1 `induce_apply_eq_self_of_mem_tiSubset` (TI-induce self-value)。
- step 2 `isDadeMap_induce_of_forall_H_eq_bot` (trivial-H hyp で Ind=Dade map)。
- step 3 `dadeMap_eq_induce_of_supported_on_trivial_H` (A₁⊆A trivial-H 上で global dadeMap=Ind、
  restrict + IsDadeMap.unique + dadeMap_restrict_apply)。
⟹ 「τ=Ind on trivial-H support」の一般 machinery 完成 (reusable)。

**残 pin (b) = 型 I final assembly のみ** (次イテレーション):
1. A₁ := 型 I A(L) の trivial-H 部分 = `{a∈A(L) : C_G(a)≤M}` = A(L)∖escapingCentralizerSet
   (supportKernel def: H(a)=L_F⊓C_G(a) if escaping else ⊥)。
2. hA₁A (A₁⊆A(L)) / hA₁norm (L normalizes A₁) / **hH₁** ((hyp.dadeData.dade.restrict).H=⊥ on A₁、
   `H_eq_supportKernel` field [S10:460] + supportKernel if-else で a∉escaping⟹⊥)。
3. **§8 support fact (cite obligation)**: φ₁−φ₂ supported on A₁ ([Is]6.2 + (8.12.a)、constituent が
   escaping 部分で消える)。data.supported は A(L)∪{1} まで。**genuine cross-lane §8、faithful sorry pin**。
4. bridge: `hyp.tau f = dadeIntegralCharacterMap .. f = hyp.dadeMap ⟨f,A-supp⟩`
   (`dadeIntegralCharacterMap_apply_of_support`) = `hyp.dadeMap (inclusion ⟨f,A₁-supp⟩)`
   (Subtype.ext、同 carrier) = `induce L f` (step 3)。
⚠ A₁ (trivial-H) と教科書の A(L)−H# が厳密一致するか要確認 (H# の定義)。

## 2026-06-29 (lane-b=β loop¹⁶): pin (b) 完全証明 ✅✅✅ — (12.4) coherence+induction machinery 完成

**pin (b) `constituent_diff_tau_eq_induce` を honest 証明** (commit 32271b67、§8 support obligation
modulo)。深い Dade machinery 全完成、残は単一 faithful §8 obligation のみ:
- 型 I bridge `typeI_tau_eq_induce_of_supported_trivial_H` (axiom-clean): step 3 を hyp.tau に
  `dadeIntegralCharacterMap_apply_of_support` で instantiate。
- escaping_conj_mem_iff (helper): escaping set L-共役不変 (既存 conj_smul_centralizer_singleton 活用)。
- pin (b) assembly: A₁=A(L)∖escaping、hA₁norm/hH₁ (restrict_H+H_eq_supportKernel+if_neg) 証明 → bridge。
- §8 obligation `constituent_diff_support_subset_nonescaping` (faithful sorried): φ₁−φ₂ が
  non-escaping 部分 supported = [Is]6.2 + (8.12.a) の genuine cross-lane 残。

**⟹ pin (a)✅ + pin (b)✅ で (12.4) 完成**。`Sset_coeff_equal` (pin a+b consume) →
`orthogonal_character_constant_on_coset` (12.4) が構造的に sorry-free (§8 modulo)。

**実装知見**: instance desync は FiniteInduce scope の `finiteGFintype` に統一 (`Fintype.ofFinite G`
を haveI で入れると hyp.tau の Fintype と非一致); `((l⁻¹:L):G)` coercion は `simpa [Subgroup.coe_inv,
mul_assoc]` で正規化 (rw [he] は coercion form 不一致); supportKernel は `show ... a.1` で arg 正規化後
`unfold; if_neg`; SupportedClassFunctions ⟨f,_⟩ は carrier 同一なら inclusion と defeq。

**残 §12 frontier (次イテレーション以降)**: (12.4) §8 obligation discharge (cross-lane §8/§10) /
(12.5) ρ-blocked (§7 ρ machinery) / (12.3) §10 support / (12.6) sibleyTarget / (12.10)-(12.16) /
(12.2.a) §8 Clifford。(12.4) は完了ゆえ次は document 順で (12.5) or §8 obligation 評価。

## 2026-06-29 (lane-b=β loop¹⁷): (12.4) 完成後の §12 frontier 再評価 — 残は deep §1/§7 prerequisites

**(12.4) 完成** (pin a✅ + pin b✅, loop¹²-¹⁶)。残 §12 sorry を survey、frontier は deep
foundational prerequisites に移行 (tractable な §12 char-coherence 核は完了):

| sorry | 内容 | 種別 |
|---|---|---|
| L855 `constituent_diff_support_subset_nonescaping` | pin b の §8 support obligation | cross-lane §8/§10 |
| L244 `typeI_induced_char_constituents` | (12.2.a) §8 type-F Clifford | cross-lane §8 |
| L348 `nonconjugate_diffImage_inner_zero` | (12.3) §10 support 不交差 | cross-lane §10 |
| L1241 `rho_constant_on_H_minus_Hprime` | (12.5) **§7 ρ machinery 要** (statement unfaithful) | deep §7 build |
| L1265 `sibleyTarget_frobI` | (12.6) Sibley target 構成 | gated on (6.8) [done?] |
| L1999-2283 (12.10)-(12.12) | structural | §8-gated (旧 lane-h) |
| L2307-2323 (12.13)-(12.16) | Dade calc + 最終矛盾 | **(12.16)=lane-b keystone**, 要 (12.5)/(1.10) |

**(12.16) `counterexample_contradiction` (lane-b keystone) の binding prerequisites** (04.14:101 精読):
(12.9)g + (1.10.a/b) p-進 congruence + (12.12) 2e≤p+1 + (12.14)/(12.15) + (7.3)/(7.8) norm bounds。

**次の最有力 target = (1.10) cyclotomic-integer congruence** (04.3:129、repo 不在、lane b 12.16 +
lane c S15/§13 両用 = 高 reuse):
- **(1.10.a)**: x order p, xy=yx, χ virtual char ⟹ `χ(xy)≡χ(y) (mod 1−ε)` in ℤ[η]。
  証明 = Res_⟨x,y⟩ χ の irreducible α は abelian ゆえ degree 1、α(x)=ε^k、α(xy)−α(y)=(ε^k−1)α(y)、
  (1−ε)∣(ε^k−1)。要: char 値 ↔ ℤ[η] bridge (ClassFunction 値は ℂ、ℤ[η]⊆ℂ への connection)。
- **(1.10.b)**: n∈ℤ, (1−ε)∣n in ℤ[η] ⟹ p∣n。証明 = N(1−ε)=p^k (mathlib `norm_sub_one_of_prime_ne_two`
  系)、(1−ε)∣n ⟹ N(1−ε)∣N(n)=n^d ⟹ p∣n。要: ℚ(η)/ℚ norm machinery (mathlib Cyclotomic.PrimitiveRoots)。
- **設計課題**: 抽象 ring R + IsPrimitiveRoot ε p で phrase か、ℤ[η]⊆ℂ 具体か。char 値の ℤ[η] 所属が
  bridge。**新 leaf** (e.g. `RepresentationTheory/CyclotomicCharacterCongruence.lean`) で cross-lane 衝突回避。
- mathlib 在庫: `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean` (norm_sub_one 系)、IsPrimitiveRoot。

substantial multi-iteration §1 build。次イテレーションで (1.10.b) [純代数、char 不要] から着手。
[[feedback-no-avoiding-hard-parts]]

## 2026-06-29 (lane-b=β loop¹⁸): (1.10) は from-scratch cyclotomic NT build と確認 + 設計確定

**確認**: (1.10) は repo に基盤なし、mathlib の cyclotomic norm も prime-power 特化 (`norm_sub_one_of_prime_ne_two` 等は p^(k+1))。char 値↔ℤ[η] bridge + p-ramification を一から構築要 = major multi-iteration。**FT-critical 確認**: (12.16)→pi_empty→typeI_frobenius(12.7)→S15_SAndT (lane c, FT-critical) consume。

**(1.10) build 設計 (次イテレーション実行)**:
- **設計課題 = ring bridge**: repo char は `ClassFunction G ℂ` (ℂ 値)。(1.10) は ℂ の部分環
  (algebraic integers `integralClosure ℤ ℂ` or `Algebra.adjoin ℤ {η}`) での divisibility。
  char 値が algebraic integer であること + (1−ε)∣(...) in 𝓞 の形式化が bridge。
- **(1.10.a)** `χ(xy)≡χ(y) (mod 1−ε)`: Res_⟨x,y⟩ χ を linear α に分解 (⟨x,y⟩ abelian)、
  α(xy)−α(y)=(α(x)−1)α(y)、α(x)=ε^k (x order p)、`(1−ε)∣(ε^k−1)` [elementary: 1−ε^k=(1−ε)∑ε^i]。
  要: char restriction + abelian-degree-1 + 値 ∈ 𝓞 (repo 薄い、要構築)。
- **(1.10.b)** `n∈ℤ, (1−ε)∣n in ℤ[η] ⟹ p∣n`: **norm approach** = `N_{ℚ(η)/ℚ}(1−ε)=p^k` (k≥1、
  N_{ℚ(ε)/ℚ}(1−ε)=Φ_p(1)=p の tower)、`N(n)=n^{[ℚ(η):ℚ]}` (`Algebra.norm_algebraMap`)、
  `N` multiplicative on `∣` ⟹ p^k∣n^d ⟹ p∣n。要: ℚ(η) IntermediateField + Algebra.norm setup。
  代替 = ring hom ℤ[η]→𝔽_p-bar (η↦ reduction, ε↦1) — prime-above-p の reduction 要、より複雑。
- **leaf**: 新 `RepresentationTheory/CyclotomicCharacterCongruence.lean` (cross-lane 衝突回避、lane b/c 両用)。

**⚠ 状況認識**: (12.4) 完了後、lane b §12 frontier は deep foundational builds のみ ((1.10) NT /
§7 ρ machinery / §8 obligations、各 multi-iteration、quick win なし)。これは §12 endgame の本来の
最難部 (lane reallocation で lane b に割当)。難所回避せず (1.10) から grind。**hub 検討事項**: lane b
§12 が deep-foundation-only になったため、reallocation 価値の再評価余地あり (但し (12.16) は assigned)。

## 2026-06-29 (lane-b=β loop¹⁹): (1.10.b) cyclotomic congruence 実装完了 ✅ — code landed

**(1.10.b) `int_dvd_of_zeta_sub_one_dvd` 完成** (新 leaf `RepresentationTheory/CyclotomicCharacterCongruence.lean`、
sorry-free)。abstract cyclotomic field 版: p odd prime, L = p-th cyclotomic field /ℚ, ζ primitive
p-th root、n∈ℤ, a integral で `n=(ζ-1)·a` ⟹ `p∣n`。
**証明 = norm argument** (設計通り): `N_{L/ℚ}(ζ-1)=p` (`IsPrimitiveRoot.norm_sub_one_of_prime_ne_two'`)、
`N(algebraMap n)=n^(p-1)` (`Algebra.norm_algebraMap` + `IsCyclotomicExtension.finrank`=totient p)、
`N(a)∈ℤ` (`Algebra.isIntegral_norm` + `IsIntegrallyClosed.isIntegral_iff`) ⟹ n^(p-1)=p·N(a) ⟹ p∣n。
mathlib API: `cyclotomic.irreducible_rat`/`Nat.totient_prime`/`Nat.prime_iff_prime_int`。

**残 (1.10)**:
- **(1.10.a)** `χ(xy)≡χ(y) (mod 1−ε)`: char restriction + (1−ε)∣(ε^k−1)。要 char 値↔algebraic-integer。
- **ℂ-instantiation bridge**: (12.16) 用に L=ℚ(ε)⊆ℂ で int_dvd_of_zeta_sub_one_dvd を適用
  (a=n/(1−ε)∈ℚ(ε)∩𝓞=ℤ[ε] の integrality 供給)。
次イテレーション = (1.10.a) char-side or ℂ-instantiation。AxiomsCheck 登録。

## 2026-06-29 (lane-b=β loop²⁰): (1.10) 残 piece scoping — (1.10.a) linear-char route + ℂ-bridge friction

**(1.10.b) 済** (loop¹⁹)。残 (1.10) piece の friction を確認:
- **ℂ-instantiation friction**: abstract (1.10.b) は cyclotomic field L 上。ℂ 適用には L=ℚ(ε)⊆ℂ の
  cyclotomic instance 要だが `intermediateField_adjoin_isCyclotomicExtension` は `[Algebra.IsIntegral ℚ ℂ]`
  要 (ℂ に transcendental ゆえ偽)。代替 = `IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot`
  (roots-set adjoin) or `CyclotomicField p ℚ`+embedding — どちらも plumbing 重。
- **(1.10.a) refined plan (char-integrality bridge 回避)**: χ(xy)−χ(y)=∑_α(α(x)−1)α(y)。
  **linear-char route**: Res_⟨x,y⟩ χ を irreducible α に分解 (⟨x,y⟩ abelian ⟹ α linear)、
  **linear char α(g) は root of unity ⟹ 直接 integral** (一般 char-integrality bridge 不要)、
  α(x)=ε^k (x order p)、(1−ε)∣(ε^k−1) [`1−ε^k=(1−ε)∑ε^i`]。要 = char restriction +
  abelian-irreducible-decomposition (repo は mathlib `Representation` ベース、要調査)。

**状況**: lane b §12 endgame は deep prerequisites の piece-by-piece grind (12.4✅/1.10.b✅ landed、
残 = 1.10.a/ℂ-bridge/§7 ρ/12.16 assembly、各 substantial)。次イテレーション = (1.10.a) linear-char
route の char restriction-decomposition から build (or ℂ-bridge)。

## 2026-06-29 (lane-b=β loop²²): (1.10.a) full の infra 全特定 — build plan 完成

**(1.10.a) full `exists_integral_zirr_apply_sub` の infra 全て特定** (de-risk 完了):
- **Fourier**: `ZIrr_eq_span` (ZIrr.lean:156、ZIrr A=span ℤ {irreducibles}) + `Submodule.mem_span` ⟹
  χ=∑ c_α α (c_α∈ℤ、Finsupp)。
- **abelian bridge**: `exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative`
  (**S11_MaximalII_III_IV:2431**、既存): abelian Γ の irreducible char φ ⟹ ∃ θ:Γ→*ℂˣ, θ(g)=φ(g)。
- **per-α core**: `exists_integral_linearChar_apply_sub` (本 leaf、loop²¹)。
**plan**: χ=∑c_α α → 各 α で bridge θ_α + linear-char core で α(xy)-α(y)=(1-ε)z_α →
χ(xy)-χ(y)=∑c_α(α(xy)-α(y))=(1-ε)·∑c_α z_α、z=∑c_α z_α integral。~100-150 行 Finsupp/span assembly。
**placement**: bridge が S11 ゆえ leaf に S11 import (heavy) か S14 内 (S14→S13→S12→S11? 要確認) に置く。
S14 closure に S11 + ZIrr_eq_span あれば S14 が自然 (lane b file)。

**(1.10) 進捗総括**: (1.10.b)✅ abstract + (1.10.a) helper✅ + linear-char core✅。残 = (1.10.a) full
(infra 全特定、次イテレーション build) + ℂ-instantiation ((1.10.b) を ℂ 値に、roots-set-adjoin route)。
これらで (1.10) 完成 → (12.16) の一前提 (他 = §7 ρ/(12.13)-(12.15)/assembly)。
**次イテレーション = (1.10.a) full を build** (infra ready、no more planning)。

### loop²³⁻²⁴ — (1.10.a) full + G-form 完成、ℂ-instantiation の field-generality 判明

**(1.10.a) 完全版 landing 済** (loop²³⁻²⁴、`CyclotomicCharacterCongruence.lean`、全 axiom-clean):
- `exists_integral_zirr_apply_sub` — (1.10.a) full: 有限群 `[Group A][Finite A][IsMulCommutative A]`
  の virtual char χ∈ℤ[Irr A]、x^p=1 で `χ(xy)-χ(y)=(1-ε)z`。**submodule framing**
  (性質を持つ CF が ℤ-submodule で irreducibles を含む ⟹ ZIrr を含む) + linear-char core。
  当初 [CommGroup] → 部分群 ↥A に適用するため **[Group]+[IsMulCommutative]** に refactor。
- `exists_integral_apply_sub_of_commute` — (1.10.a) **G-form**: 任意有限群 G、commute する x,y で
  `ψ(xy)-ψ(y)=(1-ε)z`。A=⟨x,y⟩ (abelian) に還元 (`Subgroup.isMulCommutative_closure` +
  `ClassFunction.restrict_mem_ZIrr`)。**(12.16)/(13.5) が直接 cite 可な形**。

⟹ **(1.10.a) 全形完成** (abelian + G-form)、**(1.10.b) abstract 完成**。

**🔑 残 (1.10) wiring = (1.10.b) の ℂ-instantiation。重要な設計点 (次イテレーションで対処)**:
現 `int_dvd_of_zeta_sub_one_dvd` は `[IsCyclotomicExtension {p} ℚ L]` (L = **ちょうど** p-th
cyclotomic field、[L:ℚ]=p-1、N(ζ-1)=p) を要求。だが (12.16) の char 値 z は
**ℚ(ζ_m)** (m=exp G ⊇ ζ_p) という**より大きい**体に住む (α(y) が m-th root of unity)。
norm 論法は大きい体でも成立: `N_{L/ℚ}(ζ_p-1) = N_{ℚ(ζ_p)/ℚ}(ζ_p-1)^[L:ℚ(ζ_p)] = p^[L:ℚ(ζ_p)]`
(p|N)、`N_{L/ℚ}(n)=n^[L:ℚ]` ⟹ p|n^[L:ℚ] ⟹ p|n。よって (1.10.b) を「**ζ_p を含む任意の
number field L**」へ一般化が必要 (norm tower transitivity、`Norm.Transitivity` import 済)。
**次イテレーション = この一般化版 (1.10.b) を build** (現 IsCyclotomicExtension 版は p-th 特化として残すか置換)。
Coq PFsection1 の (1.10) 対応も併読して generality 確認。

### loop²⁵ — (1.10.b) ℂ-form 完成 ⟹ (1.10) 全完成・FT-ready

**重要な statement 確定 (Coq PFsection1 併読)**: Coq は (1.10) を **ℂ の大域代数的整数**で定式化
(コメント: Z[η]→全整数環の simplification、原文 ℤ[η] と同値)。⟹ 正しい FT-usable 版は**特定体不要**:
- `int_dvd_of_one_sub_primRoot_dvd` (axiom-clean) — (1.10.b) ℂ-form: p 素数、ε 原始 p 乗根、n∈ℤ で
  `(n:ℂ)=(1-ε)·z` (z 任意代数的整数) ⟹ p∣n。前 commit の field 版 `int_dvd_of_zeta_sub_one_dvd`
  (L=ちょうど ℚ(ζ_p) 限定) は FT に使えず ⟹ **本 ℂ 版が supersede** (field 版は dead、後で除去可)。
  証明=associate-unit (Coq と同じ): `∏_{1≤k<p}(1-ε^k)=p` (mathlib `prod_one_sub_pow_eq_order`) +
  各 `(1-ε^k)∣(1-ε)∣n` (`one_sub_pow_dvd_one_sub`、整数 cofactor) ⟹ p∣n^{p-1} ⟹ ℤ descend
  (`int_dvd_of_intCast_eq_mul_isIntegral`) ⟹ p∣n。
- helper: `one_sub_pow_dvd_one_sub` (ε^k と ε の associate、gcd(k,p)=1 で ε=(ε^k)^r) +
  `int_dvd_of_intCast_eq_mul_isIntegral` (rational 代数的整数 ⟹ ℤ、IsIntegrallyClosed)。

⟹ **Peterfalvi (1.10) 全完成・FT-ready**: (1.10.a) G-form `exists_integral_apply_sub_of_commute`
+ (1.10.b) ℂ-form `int_dvd_of_one_sub_primRoot_dvd`、両者 ℂ 値指標で直接動く ((12.16)/(13.5) 用)。

**次イテレーション = (12.16) `counterexample_contradiction` 本体での (1.10) wiring に着手**: 原文
(04.14 mmd:101) の論法 — g∈C_K(x)∖K' で (1.10.a) から ψ(xg)≡ψ(g), χ(x)≡e (mod 1-ε)、(12.14) で
ψ(g)≡e、(1.10.b)+(12.15) で ψ(g)≡e (mod p)、… ⟹ 矛盾。(12.12)/(12.14)/(12.15) の現状を grep して
assembly の gate を特定。dead な field 版 (1.10.b) 除去も検討。

### loop²⁶⁻²⁸ — (12.16) を (1.10) で wiring、両端 materialize (start + end)

(1.10) 完成後、(12.16) `counterexample_contradiction` (bare sorry) の論法を engine 群で materialize
(gated 上流を仮説パラメータ化、全 axiom-clean)。**S14 が (1.10) leaf を import**。

**始端** (loop²⁶⁻²⁷): (1.10) → |ψ(g)|≥e-1。
- `psi_int_congr_e_mod_p` — (1.10.a) G-form + (1.10.b) ℂ-form + (12.14)/(12.15)/Dade 事実
  (`ψ(xg)=ψ(x)`, `ψ(x)≡e mod 1-ε`, `ψ(g)=mval∈ℤ`) ⟹ `p∣(mval-e)` (ψ(g)≡e mod p)。
- `abs_ge_e_sub_one` (純算術) + `abs_psi_g_ge_e_sub_one` (合成) ⟹ `|ψ(g)|≥e-1` ((12.12) `2e≤p+1`)。

**終端** (loop²⁸): ノルム結論 → False。
- `index_ratio_contradiction` — reduced `(|K|-|K'|)(e-1)²<e·|K|` + `4|K'|≤|K|` (fpf `[K:K']≥4`、(8.1.c))
  + e≥3 ⟹ False ((3e-1)(e-3)≥0)。
- `norm_ineq_reduce` — (12.11) `|M|≤|K||H|` 還元。`counterexample_closing` — 合成。

**gated 中間** = ノルム不等式連鎖。実は **algebra は trivial linarith**: 3 つの ρ-ノルム下界
A: `‖ψ^{ρM}‖²≥(|K-K'|/|M|)(e-1)²` (←(12.15)+|ψ(g)|≥e-1)、B: `‖ψ^ρ‖²≥1-e/|H|` ((7.8.b))、
C: `1>‖ψ^{ρM}‖²+‖ψ^ρ‖²` ((7.3)+(8.17)) から `linarith` でノルム結論。
⟹ **真の gate = A/B/C 自体 = §7/§8 ρ 機構** ((7.3)/(7.8.b)/(8.17) + §7 ρ/ρM の構成)。

**次イテレーション** = 全 (12.16) assembly engine `counterexample_contradiction_of_facts`:
始端 + 中間 (A/B/C→norm 結論の linarith) + 終端 を合成し、全 gated 事実を仮説に取って False を導く
sorry-free skeleton (gated-endpoint-skeleton パターン全体)。⟹ (12.16) の論理構造を完全 materialize、
残 sorry = §7/§8 ρ 機構の構成のみに局所化。

### loop²⁹⁻³¹ — (12.16) 全 materialize 完了 + ungated 入力 discharge、真の gate = §7 ρ 機構 (未形式化)

**(12.16) 完全 materialize** (loop²⁹): `counterexample_contradiction_of_facts` —
始端 (`abs_psi_g_ge_e_sub_one`: (1.10)→|ψ(g)|≥e-1) + 中間 (`norm_conclusion_glue`: 3 ノルム下界
A/B/C→ノルム結論) + 終端 (`counterexample_closing`) を合成、全 gated 事実を仮説化し False。sorry-free。

**ungated 入力 discharge** (loop³⁰): `two_mul_le_succ_of_odd_dvd` ((12.12) e∣p+1+odd→2e≤p+1)、
`four_le_of_dvd_sub_one` ((8.1.c) p∣[K:K']-1→[K:K']≥4)、`exists_witness_g` ((12.9) C_K(x)∖K' 抽出)。

**🔑 真の gate = §7 ρ 機構 (04.9, 完全未形式化)** (loop³¹ 調査):
`counterexample_contradiction` を閉じる残作業 = (12.16) engine の仮説のうち ρ 依存分の構成:
- hA/hB/hC (ノルム下界) = (7.3)/(7.8.b)/(8.17) + ρ/ρM 構成。
- h_const (12.14) ψ(xg)=ψ(x)、h_psix ψ(x)≡e、h_psig_int (12.15) ψ(g)∈ℤ = ρ + Dade 値理論。
- group core: (12.12) e∣p+1 導出 (F_{p²}⋊E Schur + (12.11))、(8.1.c) fpf。

**§7 ρ 機構の scope** (04.9 mmd (7.1)-(7.8)):
- (7.1) Hyp: `χ^ρ(a) = (1/|H(a)|)Σ_{x∈H(a)} χ(ax)` (a∈A)、`A^τ = ⋃_a (aH(a))^G`。
- (7.2): (a) `α^{τρ}=α` (α∈CF(L,A))。(b) `‖χ^ρ‖²≤‖χ‖²`、等号 ⟺ χ∈im τ。
- (7.3): `(1/|G|)Σ_{g∈A^τ}|χ(g)|² ≥ ‖χ^ρ‖²`、等号 ⟺ χ が aH(a) 上定数 ⟹ **bound C/(7.8.b)** の源。
- (7.5): 多 family 版 `‖χ‖²=1` 分解。
- **基盤あり**: Dade infra (`dadeSupport`/`mem_dadeSupport_iff` (base-point+H(a) 構造)/`dadeIntegralCharacterMap`)。
  ρ map 定義は H(a) を Dade hypothesis から抽出して averaging。**DadeNotation.rhoFormula/rhoMFormula は現状
  opaque Prop placeholder** ⟹ ρ/ρM を実体化する必要。
- **次イテレーション = §7 ρ map (7.1) の定義に着手** (Dade infra の H(a) 抽出 + averaging で `rho : CF(G)→CF(L)`)、
  続いて (7.2.a) adjunction → (7.2.b)/(7.3) norm bound。これが (12.14)/(12.15)/hA-hC 全ての upstream。

**(1.10) は完成済** (前 loop²³⁻²⁵、両半 FT-ready)。(12.16) は ρ 機構を残し論理構造完全。

### loop³² — §7 ρ 機構 着工: (7.1) `rhoValue` + L-conjugation 不変性 (equivariance) landed ✅

**(7.1) ρ projection の value-level API 完成** (`S07_RhoProjection.lean`、axiom-clean [AxiomsCheck
登録]、leaf+full green)。ρ 機構 = (12.16) の hA/hB/hC + (12.5) の真の gate (loop³¹ 特定) の着工。
`S07_RhoProjection` carve-out (issue 0087) stub に既存の `rhoValue` (χ^ρ(a)=(1/|H(a)|)Σ_{x∈H(a)}χ(a·x))
+ 線形性 (zero/add/smul/sub) に、**`rhoValue_conjA`** (χ^ρ(ℓ·a·ℓ⁻¹)=χ^ρ(a)) を追加 = (7.1) の
class-function (equivariance) 性質。
- **de-risk (重要)**: H-equivariance は S04 に既存 — `HConjInvariant` predicate (`H(ℓaℓ⁻¹)=ℓ·H(a)·ℓ⁻¹`)
  + `conjA` (L-action) + `mem_H_conjA_iff` (`y∈H(conjA l a)↔ℓ⁻¹yℓ∈H(a)`) + `hCoset_conj_eq`。当初の
  「H 正規 Hall 一意性を要証明」懸念は不要だった ([[verify-port-state-by-number-not-coq-name]] 同系)。
- **証明**: 共役 bijection `H(ℓaℓ⁻¹)≃H(a)` (y↦ℓ⁻¹yℓ) で average を reindex (`Fintype.sum_equiv`)、
  term ごとに `(ℓaℓ⁻¹)·y` が `a·(ℓ⁻¹yℓ)` と G-共役 (`ClassFunction.of_isConj`)、card は `Nat.card_congr`。
  **instance-desync (note 警告) は `letI iA/iB := Fintype.ofFinite _` + `rfl` で unfolded averaging form を
  pin して回避** ([[lean-induce-transport-instance-desync]] 同系の対処)。

**残 (7.1) = CF(L,A) packaging** (次イテレーション、mechanical だが fiddly): χ^ρ を `ClassFunction L ℂ`
(`⟨fun g=>if (g:G)∈A then rhoValue ⟨↑g,_⟩ else 0, conj-inv⟩`、conj-inv は rhoValue_conjA + `L_normalizes_A`
両向き [g∉A⟹ℓgℓ⁻¹∉A は h⁻¹ で戻す]) → `support⊆supportInSubgroup A L` で `SupportedClassFunctions ℂ A L`
wrap → map 線形性。**その後**: (7.2.a) `α^{τρ}=α` (Dade value `α^τ(a·x)=α(a)` = (2.10.3) `α_B`-collapse
経由) → (7.2.b)/(7.3) norm bound (adjoint/projection) → (7.8.b) → (12.16) hB/hC + (7.8) で hA。正本=issue 0081。

### loop³³ — (7.1) ρ の CF(L,A) packaging 完成 ✅ (χ↦χ^ρ が genuine な class-function map)

**`rho : CF(G) → CF(L,A)` 完成** (`S07_RhoProjection.lean`、全 axiom-clean、leaf+full green)。loop³² の
equivariance (`rhoValue_conjA`) を使い (7.1) を genuine な class-function map として実現:
- `rhoClassFun hyp hconj χ : ClassFunction L ℂ` = `⟨fun g => if (g:G)∈A then rhoValue ⟨↑g,_⟩ else 0, conj-inv⟩`。
  conj-inv 証明: A 内は `rhoValue_conjA` (`⟨↑(h·g·h⁻¹),_⟩ = conjA h ⟨↑g,_⟩` を Subtype.ext+conjA_coe で同定)、
  A 外は `L_normalizes_A` 両向き (g∉A⟹h·g·h⁻¹∉A は h⁻¹ で戻して矛盾)。**dite は `open Classical in` +
  `dsimp only` で beta 展開してから `dif_pos/neg`** (lambda 適用の未 beta で rw 失敗→dsimp で解消)。
- `rhoClassFun_apply_mem`/`_apply_not_mem` (@[simp])、`rhoClassFun_support_subset` (support⊆`supportInSubgroup A L`)、
  `rho` (= `SupportedClassFunctions ℂ A L` wrap、`mem_supportedSubmodule.mpr`)。
- 線形性 `rhoClassFun_add`/`rhoClassFun_smul` (各 by_cases (g:G)∈A + `rhoValue_add`/`_smul`、ℂ-smul=mul
  ゆえ neg 枝は `mul_zero`)。**∴ (7.1) ρ projection = value+equivariance+packaging+線形 完成**。
- AxiomsCheck 登録: `rho`/`rhoClassFun_add`/`rhoClassFun_smul`。

**残 §7 = (7.2)/(7.3) norm theory** (次イテレーション): (7.2.a) `α^{τρ}=α` (α∈CF(L,A) で
χ^ρ(a)=(1/|H(a)|)Σ α^τ(a·x)=α(a)、要 Dade value `α^τ(a·x)=α(a)` = (2.5)/(2.10.3) `α_B`-collapse の
S04 API 確認) → (7.2.b) `‖χ^ρ‖²≤‖χ‖²` (adjoint χ^{ρτ}=orthogonal projection、(2.7) Dade adjunction +
(2.6) isometry) → (7.3) `(1/|G|)Σ_{g∈Aᵗ}|χ(g)|²≥‖χ^ρ‖²` (χ₁=A^τ-restriction、χ₁^ρ=χ^ρ + (7.2.b))。
これらが (12.16) の hA/hB/hC + h_const/h_psix/h_psig_int を供給。Aᵗ=`hyp.dadeSupport` 既存。正本=issue 0081。

### loop³⁴ — (7.2.a) `α^{τρ}=α` 完成 ✅ (ρ は τ の left inverse)

**(7.2.a) `rho_dadeMap` 完成** (全 axiom-clean、leaf green)。crux = Dade τ の coset-value
`Hypothesis.dadeValue_eq` (S04:3547、`α^τ(g)=(α:CF L)⟨a,_⟩` for `IsConj (a·h) g`, h∈H(a)) が既存:
- `rhoValue_dadeMap` (value): `α^τ` は coset `a·H(a)` 上で定数 `=α(a)` (dadeValue_eq + IsConj.refl)
  ⟹ ρ-average = `(card H)⁻¹·(card H • α(a)) = α(a)` (`Finset.sum_const`+`inv_mul_cancel_left₀`、
  instance は letI+rfl pin)。
- `rhoClassFun_dadeMap` (CF(L) 形): A 上 rhoValue_dadeMap、A 外は両者 0 (rhoClassFun=0 + α supported
  ⟹ α=0 off A、`mem_supportedSubmodule`+`mem_support` で)。`⟨↑g,_⟩=g` は rw の defeq で閉。
- `rho_dadeMap` = (7.2.a): `rho hyp hconj (hyp.dadeMap α) = α` (Subtype.ext)。AxiomsCheck 登録。

**残 §7 = (7.2.b)/(7.3) norm bound** (次イテレーション): (7.2.b) `‖χ^ρ‖²≤‖χ‖²` (等号⟺χ∈im τ) は
**χ^{ρτ}=χ の orthogonal projection** を経由 — (a) で `χ^{ρτρ}=χ^ρ`、(2.7) adjunction `⟨α^τ,χ⟩=⟨α,χ^ρ⟩`
で `(α^τ, χ^{ρτ}−χ)=0` ⟹ χ^{ρτ}=proj、Pythagoras。要 = (2.7) adjunction (S04 inner_eq 系) +
(2.6) isometry。(7.3) `(1/|G|)Σ_{g∈Aᵗ}|χ(g)|²≥‖χ^ρ‖²` は χ₁=Aᵗ-restriction で (7.2.b) 適用。

### loop³⁵ — (2.7) adjunction for ρ 完成 ✅ (S04 adjoint_formula 再利用、(7.2.b) の土台)

**重要発見: S04 に (2.7) adjoint 機構が既存** — `S04.adjointAverageFun` (= ρ の underlying 関数、同式) +
`S04.adjoint_formula` ((2.7) adjunction `⟨τα,χ⟩=⟨α,ψ⟩`、docstring に「§9 (7.2.b) が直接適用」と明記)。
⟹ (7.2.b) の adjunction は再証明せず既存を cite。
- `rhoValue_eq_adjointAverageFun` (bridge、axiom-clean): rhoValue = adjointAverageFun。両者の Fintype 規約
  (Fintype.ofFinite vs instFintypeSubtypeMemOfDecidablePred) 差は `Finset.sum_congr (Finset.ext …)` で吸収。
- `rho_adjoint` = (2.7): `⟨hyp.dadeMap α, χ⟩ = ⟨α, χ^ρ⟩` (S04.adjoint_formula を ψ=rhoClassFun で cite、
  averaging hyp = bridge)。AxiomsCheck 登録。
- instance: ClassFunction.inner は `[Fintype ↥L]` (variable 追加) + `Invertible (Nat.card G/↥L : ℂ)`
  (scoped natCardInvCG/natCardInvC、S12/S15 と同パターン、S07 上流ゆえローカル宣言) 要。

**残 §7 = (7.2.b) `‖χ^ρ‖²≤‖χ‖²` の Pythagoras 本体** (次イテレーション): α=χ^ρ で adjunction
`⟨τ(χ^ρ),χ⟩=‖χ^ρ‖²` + isometry `‖τ(χ^ρ)‖²=‖χ^ρ‖²` (S04 `isDadeIsometry_of_isDadeMap`/`inner_eq`) ⟹
残差 χ−τ(χ^ρ) が τ(χ^ρ) と直交 ⟹ Pythagoras `‖χ‖²=‖χ−τ(χ^ρ)‖²+‖χ^ρ‖²≥‖χ^ρ‖²`。要 = ClassFunction
inner-self 正値性 (`∑|φ|²≥0`) + 展開。→ (7.3) → (12.16) hC。

### loop³⁶ — (7.2.b) `‖χ^ρ‖²≤‖χ‖²` 完成 ✅ (ρ は norm-decreasing、Pythagoras 一発)

**(7.2.b) `rho_normSq_le` 完成** (axiom-clean、leaf green、初回ビルド通過)。π=τ(χ^ρ) が χ の im τ 上正射影:
- adjunction `rho_adjoint` (α=rho χ) ⟹ `⟨π,χ⟩=⟨χ^ρ,χ^ρ⟩` + isometry `S04.isDadeIsometry_of_isDadeMap`
  ⟹ `⟨π,π⟩=⟨χ^ρ,χ^ρ⟩` ⟹ 残差 χ−π ⟂ π (`⟨χ,π⟩=⟨χ^ρ,χ^ρ⟩` real は `inner_conj_symm`+`inner_self_eq_realCast`)。
- Pythagoras `⟨χ,χ⟩=⟨χ−π,χ−π⟩+⟨χ^ρ,χ^ρ⟩` (`inner_sub_left/right` bilinearity + ring) → `.re` +
  `inner_self_re_nonneg (χ−π)` で linarith。
- **既存 infra 全活用**: `ZIrrFourier` の `inner_conj_symm`/`inner_self_eq_realCast`/`inner_self_re_nonneg`
  (import 追加) + S04 `isDadeIsometry_of_isDadeMap`。当初懸念した inner-self 正値性は既存。AxiomsCheck 登録。

**残 §7 = (7.3)** (次イテレーション): `(1/|G|)Σ_{g∈Aᵗ}|χ(g)|²≥‖χ^ρ‖²` は χ₁=Aᵗ-restriction
(Aᵗ=`hyp.dadeSupport`) で χ₁^ρ=χ^ρ + (7.2.b) 適用、`(1/|G|)Σ_{Aᵗ}|χ|²=‖χ₁‖²`。
→ (7.5) family / (7.8.b) → (12.16) hB/hC。

### loop³⁷ — (7.3) `‖χ^ρ‖²≤(1/|G|)Σ_{Aᵗ}|χ|²` 完成 ✅ (§7 (7.1)-(7.3) コア完結)

**(7.3) 完成** (全 axiom-clean、leaf green、初回通過)。χ₁=Aᵗ-restriction で (7.2.b) を適用:
- `restrictDadeSupport χ` = χ on dadeSupport / 0 off (conj-stable `mem_dadeSupport_conj_iff`)。
- `rhoValue_restrictDadeSupport`/`rhoClassFun_restrictDadeSupport`: χ₁^ρ=χ^ρ (χ₁=χ on coset
  a·H(a)⊆Aᵗ via `mem_dadeSupport_of_mem_hCoset`)。
- `rho_normSq_le_restrict` = (7.3): `‖χ^ρ‖²≤‖χ₁‖²` (χ₁^ρ=χ^ρ rw + (7.2.b))。
- `inner_restrictDadeSupport_re`: `‖χ₁‖²=(1/|G|)Σ_{g∈Aᵗ}|χ(g)|²` (`inner_self_eq_realCast` +
  `Finset.sum_filter` + normSq split)。⟹ 明示形 `‖χ^ρ‖²≤(1/|G|)Σ_{Aᵗ}|χ|²`。AxiomsCheck 登録。
- ⚠ unusedSectionVars: G-only の 3 lemma に `omit [Fintype ↥L] in`。

**∴ §7 (7.1)-(7.3) コア完結**: value/equivariance/packaging/linearity (7.1) + α^{τρ}=α (7.2.a) +
(2.7) adjunction + ‖χ^ρ‖²≤‖χ‖² (7.2.b) + (7.3) partial-sum bound。これが (12.16) hC の
`normRho=‖ψ^ρ‖²` + disjoint-Aᵗ 加算 → <‖χ‖²=1 の土台。

**残 §7 (12.16 用)**: (7.5) family 多重版 (Aᵢᵗ disjoint で Σ‖χ^{ρᵢ}‖²≤‖χ‖²) + (7.6)-(7.8)
family+normal-subgroup ((7.8.b) `1-e/h≤‖ζ^{νρ}‖²`=hB)。**lane γ は S09 family 機構 (`chiRho`/
`chiRhoNormSq`/`zetaNuRhoNormSq`) で (14.11.4) を処理済** ⟹ 次イテレーションは (12.16) の hA/hB/hC
を S09 family 機構 + 本 §7 (7.1)-(7.3) でどう構成するか (S09 再利用 vs (7.5)/(7.8) 新規) を評価。
正本=issue 0081。

### 🛑🛑 loop³⁸ — 重大発見: S07_RhoProjection (7.1)-(7.3) は S09 chiRho の完全重複 (STOP+報告)

**`S09_NonexistenceCertain.lean` = 教科書 §7** (S番号=§番号+2: S09↔§7)。§7 ρ machinery は `chiRho` 名で
**(7.1)-(7.8) 完備**。本セッションで S07 に構築した (7.1)-(7.3) は**完全な重複**だった (consumer は
AxiomsCheck のみ、何にも使われない):

| S07 (本セッション、冗長) | S09 既存 |
|---|---|
| `rhoValue`/`rhoClassFun`/`rho` | `chiRho`/`chiRhoCF` |
| `rho_dadeMap` (7.2.a) | `chiRhoCF_dadeImage_eq` (7.2.a) |
| `rhoValue_eq_adjointAverageFun` | `chiRhoCF_eq_adjointAverageFun` |
| `rho_adjoint` (2.7) | `chiRho_adjoint` (同じ S04.adjoint_formula cite) |
| `rho_normSq_le` (7.2.b) | `chiRho_norm_sq_le` (同じ Pythagoras) |
| `rho_normSq_le_restrict`+`inner_restrictDadeSupport_re` (7.3) | `chiRho_integral_inequality` |

さらに S09 は (7.4)-(7.8) も完備 (`FamilyHypothesis71`/`family_inequality`/`Hypothesis76`/
`Hypothesis78`/`NormEstimates` = (12.16) hA/hB/hC に必要な全部、lane γ が (14.11.4) で常用)。

**原因**: 本ノートの旧前提「S09 chiRho は family 特化、型 I A(L) 一般 ρ 不在」(loop¹⁸/²⁰) が**誤り**。
`Hypothesis71 G A L` は general single-L の (7.1) そのもの。note を信じ S09 を実コード確認しなかった
([[verify-port-state-by-number-not-coq-name]] [[scaffold-sorry-free-not-done]]、正本 memory
`s09-is-section7-chirho-complete`)。

**正しい (12.16) path**: §12 `CounterexampleHypothesis` から S09 `Hypothesis71`/`Hypothesis78` を構築 →
S09 `chiRho_norm_sq_le`/`chiRho_integral_inequality`/`NormEstimates`/`family_inequality` を cite して
hA/hB/hC を構成 (新規 ρ を作らない)。**S07_RhoProjection は削除推奨** (carve-out=issue 0087 は hub 承認
ゆえユーザー/hub 裁可待ち)。🛑 STOP し報告 (ユーザー判断待ち)。

### loop⁴⁰ — S07 削除完了 + (12.16) 配線の具体 construction plan (S09 cite、lane γ pattern mirror)

**S07_RhoProjection 削除済** (commit `4e34c478`、hub も独立に issue 0089 で削除実施 = `83c2c3c9`、merge
clean、full build 3888 green)。§7 ρ は S09 `chiRho` に (7.1)-(7.8) 完備。本来の (12.16) 配線へ。

**(12.16) 原文 (04.14 L99-101) の構造** (精読確定):
- (12.13): S={Ind_H^L θ}, τ=Dade isometry for (A(L),L,G), τ₁ 拡張 (by (12.6)), χ∈S with χ(1)=e, ψ=χ^{τ₁},
  ρ=(7.1) map with A=A(L)。
- (12.14): ψ(xg)=ψ^ρ(x)=χ(x) for g∈K。 (12.15): ρ_M=(7.1) map for (M, A₁(M)); ψ^{ρ_M}(g)=ψ(g) on K#,
  ψ const on K-K', ψ(g)∈ℤ。
- (12.16): (1.10) + norm bounds で |ψ(g)|≥e-1 → (7.3)/(7.8.b) で矛盾。**ρ (for L) と ρ_M (for M) の
  2 つの (7.1) map を使う**。

**construction plan (lane γ MHypothesis pattern を mirror、全て S09 cite)**:
- **producers 既存**: `S12.Hypothesis.toHypothesis71` (S12:440)/`toFamilyHypothesis71` (S12:458) =
  §10-13 char hyp → S09 `Hypothesis71`/`FamilyHypothesis71`。lane γ `MHypothesis` (S16:1585) は
  `h78:S09.Hypothesis78` をバンドルし `NormEstimates.zetaNuRho_norm_sq_ge` で (7.8.b) を得る = **(12.16)
  hB の template**。
- **hB ((7.8.b) for L)**: witness L (Frobenius, (12.10)) + S coherent ((12.6)) から `Hypothesis78 G (A(L)) L`
  を構築 → `NormEstimates.zetaNuRho_norm_sq_ge` cite。**bottoms out on (12.6)/(12.10) sorries** (signature
  contract で cite 可、[[feedback-cite-sorried-lemmas-if-signature-correct]])。
- **hA ((12.15) for M, ρ_M)**: `Hypothesis71 G (A₁(M)) M` (M type-I、S12.toHypothesis71 系) → ψ^{ρ_M}。
- **hC ((7.3)/(7.5))**: 両 pole の Aᵗ disjoint → `family_inequality` (S09) / `chiRho_integral_inequality`。
- **始端/終端は materialize 済** (`counterexample_contradiction_of_facts` sorry-free、(1.10) 完成)。

**残骨格**: `counterexample_contradiction` (S14:2491) を `exists_rankTwoWitness` (S14:1948) で witness 取得 →
ψ=χ^{τ₁} 構築 → hA/hB/hC を上記 S09 cite で構成 → `counterexample_contradiction_of_facts` 適用。
**多 iteration の deep endgame** (Hypothesis78 構築 + ν coherent extension + ζ distinguished が核)。
次イテレーション = witness 取得 + skeleton (facts を faithful obligation に isolate) から着手。正本=issue 0081。

### loop⁴¹ — (12.16) capstone を sorry-free assembly 化 (witness 実配線 + facts contract isolate)

**commit `61e38330`**: `counterexample_contradiction` (S14:2554) は**もう sorry-free**。残骨格 = 単一 producer
`exists_counterexample_dade_data` (S14:2541) に集約された。

**現 (12.16) frontier の構造** (full build 3888 green, AxiomsCheck OK):
```
counterexample_contradiction (2554, sorry-FREE)
 ├ exists_rankTwoWitness (1948, sorry-free)        ← witness (rank-2, x, L)
 ├ exists_witness_g (2479, sorry-free)             ← g∈C_K(x)∖K', Commute x g
 ├ exists_counterexample_dade_data (2541, ★SORRY)  ← 唯一の残 deep obligation
 └ counterexample_contradiction_of_facts (2440, sorry-free)  ← 数値 endgame 完成済
```

**残 obligation = `CounterexampleDadeData` (2502) の全 field 構成** (structure = 12.13–12.16 の精密契約)。
次 iteration の充足順 (易→難、全て field 単位で per-field 充足可能):
1. **易 (real proof 即可、ψ 不要)**: `ε`/`hε` = `Complex.isPrimitiveRoot_exp ctr.p` 系;
   `kK/kKp/kM/kH` = `Nat.card` 実値 + 正値性 (`Nat.card_pos`)。→ producer を `refine {ε:=…, …, ψ:=?_, …}`
   で部分実体化し deep field のみ per-field sorry に分離するのが honest。
2. **群論 (char 不要)**: `hidx` = (8.1.c) fpf `4|K'|≤|K|` (`four_le_of_dvd_sub_one` 既存); `hM` = (12.11)
   `intersection_complement_structure` (2009 sorried, signature cite 可) から `|M|≤|K||H|`。
3. **char 核 (deep, 多 iteration)**: `ψ`/`hψ` = DadeNotation (12.13) の ψ=χ^{τ₁} 構築 (`Hypothesis data.L`
   要、data.L type-I は `witness_L_frobenius` (12.10)); `e`/`he`/`h2e` = (12.12) degree; `h_const` =
   `psi_constant_on_xK` (12.14, 2308 sorried); `h_psig_int` = `rhoM_integer_values` (12.15, 2317);
   `hA` = (12.15) ρ_M norm; `hB` = (7.8.b) `S09.NormEstimates.zetaNuRho_norm_sq_ge` (Hypothesis78 構築);
   `hC` = (7.3) `S09.chiRho_integral_inequality`。lane γ `MHypothesis` (S16:1585) pattern を mirror。

### loop⁴² — witness L の Dade+coherence foundation 確立 (hB への配線完了)

**commit `fac8de5d`**: (12.16) char 核に向け、witness 第二極大 L の Dade machinery を named lemma 化:
- `hypothesis_of_typeIData` (S14:159, sorry-free): explicit `TypeIData` → `Hypothesis L` + `hyp.typeI=data`
  保存。`exists_typeI_hypothesis` を本 lemma 経由に refactor。**型 I witness の identity 保存が鍵** —
  Nonempty 版は erase するため Frobenius 構造を hyp.H に transfer 不能だった。
- `witness_L_hypothesis_frobenius` (S14:~2015): L は (12.10) で type-I ゆえ `Hypothesis data.L` +
  `∃C, IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C`。
- `witness_L_hypothesis` (forgetful)、`witness_L_coherent`: (12.6) `frobenius_typeI_coherent` 合成で
  `Nonempty (S07.IsCoherent hyp.tau hyp.Sset hyp.A)`。S12.FiniteInduce scope で instance 自動。

**これで `CounterexampleDadeData` の char 核への入力が揃った**: hyp (Dade isometry hyp.tau / 族 hyp.Sset /
support hyp.A) + coherence。残るは:
1. **hB = (7.8.b)**: coherence → `S09.Hypothesis78 G (A(L)) L` 構築 → `NormEstimates.zetaNuRho_norm_sq_ge`。
   次 iteration の標的。lane γ `MHypothesis` (S16:1585) の h78 bundle pattern を mirror。**S09.Hypothesis78
   の field 要件 + coherence からの構築経路を調査**するのが次の一歩。
2. **DadeNotation 構築**: distinguished χ∈Sset (degree e) + 拡張 τ₁ → ψ=τ₁(χ)。(12.13) data。
   e の degree bound (12.12) `complement_cyclic_order_dvd` (sorried) が he/h2e を供給。
3. **hA/hC**: ρ_M norm (12.15) / `chiRho_integral_inequality` (7.3)。

### loop⁴³ — S14.Hypothesis.toHypothesis71 完成 ((7.1) foundation)

**commit `00c37192`**: `S14.Hypothesis.toHypothesis71` (S14:~102, sorry-free) = type-I L の (7.1)
`S09.Hypothesis71 G (typeIA L hyp.typeI) L`。type-P (S12) と違い restriction 不要 (typeIA が dadeData の
載る set そのもの)。`dadeData.dade : S04.Hypothesis G (typeIA L typeI) L` 直接 + FullDadeIsometryData の
`.toDadeIsometryData.{toDadeMap,isDadeMap}` で構築。

**hB への残 chain (構築コスト順)**:
1. **Hypothesis76** (族 T): `hyp71`(済) + `H`/`A_eq_H_sharp`/`n`/`zeta`/`d`/`zeta_one_eq_d_mul`/
   `psi_support`/**`chiRho_decomp`** ((7.7.a) decomposition 証明書)。H=L_F、T=Ind 構成要素列挙。
   **族列挙 + (7.7.a) が実質 character theory ゆえ multi-step** (一 iteration 不可)。
2. **Hypothesis78** (ν+certificate): Hypothesis76 + `nu`(coherent isometric extension, witness_L_coherent
   の IsCoherent から)+ distinguished ζ + **`chiRho_eq_inner_beta`** ((7.8.c.i) certificate)。
3. **hB**: `NormEstimates.zetaNuRho_norm_sq_ge` (S09:2616) cite。

**次 iteration の標的**: Hypothesis76 構築の足場。H=L_F の特定、族 T (n/zeta/d) の (7.6) 列挙、
chiRho_decomp (7.7.a) の構築経路調査。lane γ MHypothesis.h78 は obligation field ゆえ exists_MHypothesis
での discharge 法 (S16:4499) も参照。

### loop⁴⁴ — dadeNotation_of_coherence (ψ=χ^{τ₁} backbone を coherence から実現)

**commit `23c49c3a`**: 重要発見 = `S07.IsCoherent.extension : IntegralCharacterMap ↥L G` が (12.13) の
τ₁ そのもの (S07_Coherence:1596、`extension`/`extension_inner_eq`/`extends_on_supported` フィールド)。
`dadeNotation_of_coherence` (S14:~2368): coherence + distinguished χ∈Sset(deg e) → DadeNotation を
tau1:=coh.extension / psi:=coh.extension χ で構築 (**psi_eq_tau1_chi := rfl**)。e_eq_index を e=[L:H] に
de-opacify。

**調査確定事項 (次 iteration の地図)**:
- **ψ-construction の残 gap = distinguished χ 選択のみ**: Sset={Ind_H^L θ | θ irred ≠1} (S14:84)。
  distinguished χ は最小 degree=[L:H] ゆえ **θ 線形 (deg 1)** が必要。H=L_F は非自明 nilpotent ゆえ
  H/[H,H] 非自明 → 非自明線形指標 θ 存在。`χ(1)=[L:H]·θ(1)=[L:H]` は `induce_apply_one`
  (RepresentationTheory、Ind θ(1)=[G:H]θ(1)) で。**次 iteration の標的 = exists_distinguished_char**
  (非自明 nilpotent 群の非自明線形指標存在 + induce degree)。mathlib の linear char / abelianization
  character API 要調査 (未確認)。
- **hA/hB/hC は全て ψ 前提** (確定): hB=(7.8.b) lower bound は Hypothesis78 必須で、その
  chiRho_eq_inner_beta (7.8.c.i)/chiRho_decomp (7.7.a) は **project 全体で未形式化**
  (lane γ exists_MHypothesis (S16:4502) も h78 含む全体を単一 sorry で defer)。
  (7.2.b)/(7.3) は upper bound (proven) ゆえ hB には不足、hC(sum<1)には寄与し得る。
- **(12.12) degree bound** `complement_cyclic_order_dvd` (S14 sorried) が he:3≤e/h2e:2e≤p+1 を供給。
  rep-theory cores (isCyclic_and_card_dvd_of_faithful_one_dim 等 S14:2015+) から組める可能性。

### loop⁴⁵ — ψ=χ^{τ₁} を witness L で完全構築 (distinguished χ 解決)

**commit `0225855a`**: ψ-construction が realize された:
- `exists_distinguished_char` (S14:~2392, sorry-free, 実 character theory): S が最小 degree [L:H] の member
  を含む。H=L_F 非自明 nilpotent → commutator≠⊤ → `S08.exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`
  (推移 import 済; 内部は CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity = Pontryagin) で非自明線形
  θ → χ=Ind θ、`induce_apply_one` で degree=[L:H]。**instance desync 教訓**: Sset の induce と同じ
  FiniteInduce scope `natCardInvC` を使え (explicit invertibleOfNonzero は別 instance → rfl 破綻)。
- `exists_witness_dadeNotation` (S14:~2425, sorry-free assembly): witness_L_coherent + exists_distinguished_char
  + dadeNotation_of_coherence → witness L が完全 DadeNotation (ψ=χ^{τ₁})。

**(12.16) char 核の残 (CounterexampleDadeData の値/norm 内容)**:
- **h_const** = (12.14) `psi_constant_on_xK` (S14 sorried) — ψ concrete 化したので証明可能性 up。
- **h_psig_int** = (12.15) `rhoM_integer_values` (S14 sorried)。
- **e/he/h2e** = (12.12) `complement_cyclic_order_dvd` (S14 sorried) — rep-theory cores
  (isCyclic_and_card_dvd_of_faithful_one_dim 等 S14:2015+) から組める見込み = **次の自己完結な実標的**。
- **hA/hC** = ρ_M norm (12.15) / chiRho_integral_inequality (7.3, proven, Hypothesis71 から)。
- **hB** = (7.8.b) lower bound = Hypothesis78 必須 → (7.7.a)/(7.8.c) certificate は **project 全体で未形式化**
  (真の hard floor; lane γ も defer)。ここが (12.16) を closeする最終 blocker。

**次 iteration の標的**: (12.12) `complement_cyclic_order_dvd` を rep-theory cores から組む (he/h2e 供給)。

### loop⁴⁶ — hψ:ψ∈ZIrr G 追加 (ψ-data package 完成) + 戦略評価

**commit `30be6dc9`**: `exists_witness_dadeNotation` を (hyp, dade, dade.psi∈ZIrr G) に拡張。
IsCoherent.extension_mem_ZIrr (ℤ[S]→ℤ[Irr G]) を distinguished χ∈zSpan S に適用。
witness L の ψ-data (ψ=dade.psi / e=dade.e / hψ) が CounterexampleDadeData 構築に揃った。

### ⚠ (12.16) char 核の戦略評価 (loop⁴⁰–⁴⁶ 累積後)

**到達済 (sorry-free real)**: capstone assembly + contract / witness L の Dade+coherence /
toHypothesis71 ((7.1)) / dadeNotation_of_coherence / distinguished χ / **ψ=χ^{τ₁} 構築** / hψ∈ZIrr。

**CounterexampleDadeData の残 field を到達可能性で分類**:
| field | 内容 | 状態 |
|---|---|---|
| ε/hε | primitive root | **easy real** (Complex.isPrimitiveRoot_exp) |
| ψ/hψ | χ^{τ₁}, virtual | **DONE** (exists_witness_dadeNotation) |
| e | [L:H] | **DONE** (dade.e) |
| h_const | (12.14) ψ(xg)=ψ(x) | char-deep (psi_constant_on_xK sorried、ψ concrete 化で証明可能性 up) |
| h_psig_int | (12.15) ψ(g)∈ℤ | char-deep (rhoM_integer_values sorried) |
| he/h2e | (12.12) 3≤e, 2e≤p+1 | **deep**: complement_cyclic_order_dvd は T=Ω₁(Z(O_p(H))) 構築+FPF+p²−1→p+1 refinement (12.9/12.11消費) |
| h_psix | (1.10.a) Dade value 合同 | char-deep |
| 基数/hidx/hM | \|K\|等, (8.1.c), (12.11) | 群論 (cite 可、一部 real) |
| hA | (12.15) ρ_M norm | char-deep |
| **hB** | **(7.8.b) lower bound** | **🛑 HARD FLOOR**: Hypothesis78 の chiRho_eq_inner_beta (7.8.c.i)/chiRho_decomp (7.7.a) は **project 全体で未形式化** (lane γ exists_MHypothesis も全体 sorry)。(12.16) を closeする最終 blocker |
| hC | (7.3) sum<1 | chiRho_integral_inequality (proven) から組める可能性 |

**🛑 戦略判断ポイント**: (12.16) の完全 close は **hB = (7.8.c) (7.7.a) の形式化を要し、これは §7 (S09) の
project 全体の hard floor** (lane γ と共有)。lane b 単独では (12.16) を閉じられない。選択肢:
(a) 12.16 の到達可能 field (12.14/12.15/12.12) を引き続き埋める (honest だが hB は残る)、
(b) 上流 (7.8.c)/(7.7.a) の形式化に pivot (§7、深い、lane γ も unblock するが S09 領域)。
上流優先原則は (b) を示唆するが S09 は別領域。**ユーザー判断が望ましい** (現状は (a) を継続中)。

### loop⁴⁷ — three_le_index (he:3≤e) 完成

**commit `53605390`**: `three_le_index` (sorry-free) = CounterexampleDadeData の `he : 3 ≤ e`。
e=[L:H]=|U| (Frobenius complement、typeF.complement.symm.index_eq_card)、非自明 (U_nontrivial) ∧
奇数 (∣|G| odd) → ≥3。**field 表更新: he = DONE**。残 reachable: ε/hε (easy), 基数/positivity (easy),
h_const(12.14 cite)/h_psig_int(12.15 cite)/h2e(12.12)/hidx(8.1.c)/hM(12.11) = cite-able。
**trajectory**: 残り cite-able を埋めて exists_counterexample_dade_data を hA/hB/hC のみ残す real partial
assembly にする (hB=hard floor を明示 isolate)。次: ε/hε + 基数 (easy reals)。

### loop⁴⁸ — lane b 方向転換: §7 hard floor 解消へ (ユーザー裁可)

**ユーザー判断 (AskUserQuestion)**: lane b の (12.16) ψ-construction (he/hM 含む) 完了後、残る hard floor
**hB=(7.8.b) は `Hypothesis78` の (7.8.c.i) certificate を要し project 全体で未形式化**。ユーザーが
「§7 hard floor を解消」を選択 → lane b を **§7 (7.7.a)/(7.8.c) certificate discharge に pivot**。

**正本 = issue 1013** (S09 §7 certificate discharge)。要点:
- hard floor = `Hypothesis76.chiRho_decomp` (7.7.a) + `Hypothesis78.chiRho_eq_inner_beta` (7.8.c.i) が
  構造の carried field。coherence から Hypothesis76/78 を構成するにはこれらを証明要。
- 原文 mmd `04.9` L54-109 (p.39-40) に proof。coq `PFsection7.v` 併読。
- ⚠ S09 は別セッションが活発編集中 ((7.11) assembly) → **S09 直接編集せず新ファイルで certificate を
  standalone theorem 証明**して衝突回避。
- discharge 後、lane b (12.16) hB と lane γ (14.11) h78 obligation の両方が unblock。

**(12.16) の lane b 成果は temporal に一段落** (ψ/he/hM real、残 field は §7 unblock 待ち or deep)。
次イテレーション = (7.7.a) chiRho_decomp の standalone 証明に着手 (新ファイル)。

### loop⁴⁹ (2026-07-01 lane-b resume²): §7 完了 → §12 char frontier map + 次標的確定

**§7 certificate discharge 完了** (hzeta0nu + witness_L_zeta_bound、commit 58de8be2/285232d7)。
lane-b frontier を §12 char 残 sorry に移す。**frontier map (全 gate 調査済)**:
- **12.11** intersection_complement_structure: **(8.13.c1)** [absent, "L=L_F⋊(M∩L)"] gated。
- **12.12** complement_cyclic_order_dvd: 12.10/12.11 + T=Ω₁(Z(O_p(H))) p-group 構成 gated
  (rep-theory core=my p+1 は済)。
- **12.14** psi_constant_on_xK: **CharacterDecompositionData** (M-side) 経由 (12.3 proven+12.4 proven
  で ψ⊥R(χ_M)→constant on xK)。CharacterDecompositionData は **typeI_induced_char_constituents (12.2.a)**
  producer 不在で gated。
- **12.15** rhoM_integer_values: **rhoMFormula opaque Prop** (faithful 化要) + ρ_M。
- **12.2.a** typeI_induced_char_constituents: 一般 type-I は **(8.2.c)** [I(θ)∩U⊆U₁, §8 型 F inertia]
  gated。**ただし Frobenius L (witness=12.10, 相当 consumer) では χ=Ind θ が既約 ⟹ 構成要素は自明
  (単一 = χ 自身)**、非実=奇位数 (`not_isReal_of_ne_trivial_of_odd_card'`, 済ツール)、
  support=K normal ゆえ Ind は K 外で消える → K^# ⊆ supportInSubgroup (mem_supportInSubgroup_sharp_subgroupOf_iff)。

**⭐ 次標的 = `frobenius_characterDecompositionData` (Frobenius 版 12.2.a producer)**: 
`(hyp)(hfrob: IsFrobeniusGroup ↥L K C)(χ∈Sset) → CharacterDecompositionData hyp χ`。5 field 全て
Frobenius+奇位数で構成可能 ((8.2.c) 不要)。これで witness-L の (12.3)/(12.4) 応用 (→ψ⊥R(χ)→coset
constant) が unblock、12.14 の witness-side path が開通。一般 type-I (非 Frobenius) の (8.2.c) は別 gate。

### loop⁵⁰⁻⁵¹ (2026-07-01 lane-b resume²): L-side (12.2.a) 完了 + M-side (8.2.c) proof map

**L-side landed** (commit 2ce97734/042e06df, sorry-free axiom-clean):
- `frobenius_induce_char_singleton` (clean-instance helper): 奇 Frobenius Γ で非自明 Ind_H^Γ θ は
  単一既約 ξ (opaque)、非実、support⊆H (正規)。FiniteInduce scope whnf 回避。
- `frobenius_typeI_induced_char_constituents` + `frobenius_character_decomposition_and_dade_domain`:
  Frobenius L の CharacterDecompositionData を (8.2.c) なしで sorry-free 構成。

**(12.16) critical path 確認**: 12.14 は L-side (ψ∈ℤ[R(χ_L)] via (5.5) + R(χ_L)⊥R(χ_M) via (12.3
proven)) **と** M-side ((12.4)-for-M、M の CharacterDecompositionData) の両方を要す。L-side data は
上記で ready。残 critical path 2 件:
- **(5.5)** [§5, ψ∈ℤ[R(χ)]]: 文書順で (8.2.c) より上流。S07 coherence 機構に在庫確認要 (次)。
- **(8.2.c)** [§8, I(θ)∩U⊆U₁ type-F inertia]: M-side data の gate。**proof map (mmd 04.10)**:
  g∈U-U₁ ⟹ g は H の非自明 class を normalize しない (C={1}、(2.1) coprime action + Frobenius
  complement 構造) ⟹ **Brauer 6.32** (`card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`
  = ConjugationBrauer.lean:186、**在庫**) で #g-invariant char = #g-invariant class = 1 ⟹ θ≠1 は
  g-invariant でない ⟹ g∉I(θ)。**key 材料 (Brauer 6.32 + (2.1)) は在庫**、残は TypeFData の U₀/U₁
  構造 exposure + C={1} step。focused §8 effort (multi-iteration)。

### loop⁵²⁻⁵³ (2026-07-01 lane-b resume²): (8.2.c) 完全 scoping — 全 piece 特定、proof 確定

**(8.2.c) I(θ)∩U⊆U₁ は tractable、全 infrastructure 特定済**。次 iteration で実装:

**必要 piece (全在庫 or 明確)**:
- `centralizer_le_U1` = TypeFData **field** (`∀ x∈H, x≠1 → U⊓C_G(x)⊆U₁`)。crux。
- Brauer chain **完全在庫** (ConjugationBrauer.lean):
  - `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm` (Brauer 6.32)。
  - `fixed_irreducible_eq_trivial_of_card_fixedClasses_eq_one` (#fixed class=1 ⟹ fixed char=trivial)。
  - `fixed_eq_one_of_not_mem_of_centralizer_le` (**Frobenius 版**、C_G≤H 条件、type-F 版に adapt 要)。
- (2.1) conjugacy form = `coset_eq_cosetConjImage` (S04、Hg=⨆(C_H(g)g)^x)。
- π-part step `g=(zg)^m` (z∈C_H(g), coprime): mathlib Commute+coprime power (要検索/構築、~数行)。

**proof (type-F class-fixing variant, fixed_eq_one_of_not_mem_of_centralizer_le の type-F 版)**:
g∈U-U₁, g fixes class ⟦h⟧ (h∈H^#) ⟹ ∃c∈H, cg∈C_G(h) [Frobenius 版と同じ導出] ⟹ (2.1
coset_eq_cosetConjImage) cg~zg (z∈C_H(g)、y∈H で (cg)^y=zg) ⟹ zg centralizes h^y ⟹ g=(zg)^m ゆえ
g centralizes h^y∈H^# ⟹ g∈U⊓C_G(h^y)⊆U₁ (centralizer_le_U1) 矛盾。⟹ #fixed class=1 ⟹
(Brauer) θ≠1 not g-inv ⟹ g∉I(θ)。∴ I(θ)∩U⊆U₁ (contrapositive: g∈I(θ)∩U ⟹ g∈U₁)。

**inertia↔conjByPerm 接続**: g∈I(θ) ⟺ IrreducibleCharacter.conjByPerm g θ = θ (Inertia.lean +
ConjugationBrauer の conjByPerm 定義、要 bridge 確認)。

**scope**: type-F class-fixing variant (~40-60 行) + π-part helper。M-side data
(typeI_induced_char_constituents 一般版) は (8.2.c) + Clifford decomp を要すので (8.2.c) は 1 input。

### loop⁵⁴⁻⁵⁶ (2026-07-01 lane-b resume²): ✅ (8.2.c) 完全証明 — M-side gate 突破

**(8.2.c) `typeF_inertia_inf_le_U1` (I(θ)∩U⊆U₁) を sorry-free + axiom-clean で完全証明**
(commits 43a28f4d/da833a9a/8c8688d4)。§12 char frontier の M-side critical-path gate 突破。
- `mem_zpowers_mul_of_commute_coprime` (π-part、汎用 GT)。
- `fixed_conjClass_eq_one_of_typeF` (核): g∈U-U₁ は自明 H-class のみ固定 ((2.1) exists_mem_centralizer_conj
  + π-part + centralizer_le_U1 field)。
- `card_fixedPoints_conjClassPerm_eq_one_of_typeF` + `typeF_inertia_inf_le_U1` (Brauer chain +
  IrreducibleCharacter.coe_conjBy inertia bridge)。

**残 = 一般 typeI_induced_char_constituents (S14:~350 sorry)**: (8.2.c) は **equal degree** input
(inertia bound ⟹ 構成要素の共通次数)。だが**構成要素の decomposition 自体は Clifford theory** 要
(Ind_H^L θ の constituents = I_L(θ)/H 構造)。次: (a) Clifford decomposition (clifford_decomposition
在庫、Ind の constituents 列挙)、(b) (8.2.c) を TypeFData field (Hall coprime hUHcop + centralizer_le_U1)
に接続、(c) equal degree/support/non-real 組み上げ。これで M-side CharacterDecompositionData →
12.14 の (12.4)-for-M 応用が開通。

### loop⁵⁷ (2026-07-01 lane-b resume²): 一般 typeI_induced_char_constituents 残 = induced-char Clifford (substantial fresh effort)

**(8.2.c) は completed** (equal-degree input ready)。だが一般 typeI_induced_char_constituents は
**Ind_H^L θ の構成要素 decomposition** を要し、これは既存 `clifford_decomposition` (Clifford.lean、
**Res_H χ = e·Σθ の restriction 版**) の **dual** = 誘導指標の構成要素列挙で、repo に readily 不在。
substantial な Clifford-theory build (誘導指標 → 構成要素、(8.2.c) で equal degree、multiplicity) が要る。

**次 focused effort の scope** (fresh session 推奨):
- 誘導指標 Ind_H^L θ (H◁L) の構成要素 = I_L(θ) 上の Clifford 対応。(8.2.c) I(θ)∩U⊆U₁ で
  I_L(θ)=H·(I(θ)∩U)⊆H·U₁ を bound → 構成要素の共通次数 [L:I_L(θ)]·(...)。
- 既存 machinery: `card_mul_inner_self_induce_eq_card_inertia` (‖Ind θ‖²=[I_L(θ):H])、
  `inner_induce_eq_zero_of_not_conj`、CliffordSingleOrbit。誘導版 decomposition producer は未在。
- L-side (Frobenius) は済 (frobenius_typeI_induced_char_constituents、I_L(θ)=H 自明)。
  一般 (I_L(θ)>H) が残。

**セッション成果 (全 committed, build-green, axiom-clean)**: §7 hzeta0nu → witness_L_zeta_bound (hB) →
L-side (12.2.a) → π-part helper → **(8.2.c) typeF_inertia_inf_le_U1 (M-side gate、hard §8 実証明)**。

### loop⁵⁸ (2026-07-01 lane-b resume²): 残 critical-path 2 件は共に sustained build — frontier map 確定

(5.5) と一般 typeI_induced_char_constituents の両方の tractability を精査し確定:
- **(5.5)** [ψ=χ^{τ₁}∈ℤ[R(χ_L)]]: `CharacterPsiDecomposition` (S07:1173、(5.4) の X/Y 分解) の
  ψ=0 case で得られる。X:=Σ_{α∈imageSet}(proj.choose α)•α ∈ span R(χ)。build path: witness χ_L で
  CharacterPsiDecomposition.ofProjection (ψ=0) 構成 → Y=0 → χ^{τ₁}=X∈span_ℤ imageSet。~30-50 行の §5 build。
  **最もクリーンな次 build** (machinery 在庫、L-side、文書順上流)。
- **一般 typeI_induced_char_constituents (M-side)**: 誘導指標 Clifford decomposition が要り (既存は
  restriction 版のみ)、+ (8.2.c) を M の TypeFData に subgroupOf 接続 (↥M で H=M_F normal)。substantial。

**両者 sustained multi-iteration build** (60s loop increment でなく dedicated effort 向き)。
(8.2.c) までの成果は全 committed・build-green・axiom-clean。次 dedicated session の第一歩 = (5.5) via
CharacterPsiDecomposition.ofProjection (witness χ_L, ψ=0)。

### loop⁵⁹ (2026-07-01 lane-b resume²): (5.5) build recipe 完全確定 (次 dedicated session の第一歩)

**(5.5) `eq_sum_of_psi_eq_zero` (S07:1561) は既存** — witness で使うには CharacterPsiDecomposition を
ofProjection で構成して適用するだけ。**完全 recipe**:
```
-- witness hyp/coh (witness_L_coherent), 区別 χ_L=Ind θ₀ (exists_distinguished_char), hfrob (12.10)
-- 1. χ_L を IrreducibleCharacter 化: ⟨Ind θ₀, isIrreducibleCharacter_induce_of_frobeniusGroup⟩
-- 2. imageFamily := dadeOrthonormalCharacterImageFamilyOfDiff hyp.dadeData.dade hyp.hconj χ_L
--      hreal (not_isReal_of_ne_trivial_of_odd_card' 奇位数) hdiffsupp (χ̄_L-χ_L ⊆ A、induce_diff_support 系)
-- 3. D := CharacterPsiDecomposition.ofProjection imageFamily coh.extension
--      htau1_inner_eq (coh.extension_inner_eq: χ_L,χ̄_L∈zSpan S ⟹ isometry)
--      htau1_agrees (coh.extends_on_supported: χ_L-χ̄_L supported)
--      htau1_mem (coh.extension_mem_ZIrr χ_L)  hχψ/hχbarψ (inner_zero_right)  hχχbar (⟨χ_L,χ̄_L⟩=0 非実)
-- 4. eq_sum_of_psi_eq_zero D ⟹ coh.extension χ_L = D.X = Σ_{α∈E⊆imageSet} α ∈ span_ℤ R(χ_L)
```
~60 行 dedicated build。全 input 特定済 (dadeOrthonormalCharacterImageFamilyOfDiff / ofProjection /
eq_sum_of_psi_eq_zero 在庫)。これで ψ∈ℤ[R(χ_L)] (12.14 L-side) が landing。

**残 critical-path map (全 scoped)**: (5.5) [上記 recipe、L-side] → 12.14 は + M-side ((12.4)-for-M、
一般 typeI_induced_char_constituents via induced-char Clifford + (8.2.c) 接続) → 12.16。

### loop⁶⁰ (2026-07-01 lane-b resume³): ✅ (5.5) L-side + horth-combine 完成 — 3 lemma landing

loop⁵⁹ recipe を実装し、(12.14) L-side wiring を確定 (全 build-green、+157 行, 2 commit):

1. **`coherent_extension_mem_span_imageFamily`** ((5.5) 核, 一般形, **axiom-clean**): 非実
   `χ∈S` + coherent `coh` で `coh.extension χ ∈ span ℤ R(χ)`。ψ=0 の `CharacterPsiDecomposition.ofProjection`
   (τ₁=coh.extension, 唯一の数論入力 = `extension_mem_ZIrr` — 一般 unsupported X-family が欠く virtual-char 性)
   → `eq_sum_of_psi_eq_zero` で Y=0 → χ^{τ₁}=X=Σ_{α∈E⊆R(χ)}α。recipe 通り、build 一発 (defeq 全通過)。
2. **`coherent_extension_constituent_mem_span_Rset`** (Rset bridge, **axiom-clean**): 構成要素
   `φ∈S(χ)∩S` で `coh.extension φ ∈ span ℤ (Rset data)`。(5.5) image family は R1 data hφ と
   **defeq** (同一 dadeCharacterDifferenceImageOfDiff, proof-irrelevant support 入力) → span_mono。
   ⟨φ,φ̄⟩=0 は `data.not_real` から自動 (非実既約⊥共役、conjPerm 経由)。
3. **`coherent_extension_constituent_orthogonal_Rset_of_nonconjugate`** (horth-combine): 非共役
   L,M で `∀α∈Rset data_M, ⟨coh_L.extension φ_L, α⟩=0`。(5.5)[2] + (12.3)
   `nonconjugate_typeI_R_orthogonal` + `inner_eq_zero_of_mem_zSpan` + conj-symm。body sorry-free
   だが (12.3) の geometric obligation `nonconjugate_diffImage_inner_zero` (8.18.c, §10=lane-d) を
   signature-contract cite ⟹ sorryAx transitively (axiom-clean block 外, コメント明記)。

**これで (12.14) `psi_constant_on_xK` の horth (ψ⊥R(χ_M)) の L-side は確定**。残 (12.14)→(12.16):
- **M-side data**: `typeI_induced_char_constituents` (S14:389, sorry) = 一般 induced-char Clifford
  decomposition (Ind_H^L θ → 等次数・非実・A(L)∪{1}-supported 構成要素)。**次の deep frontier**。
  (8.2.c)[done] + (1.7.c) 誘導次数 + (1.5.a)/(1.2) support。既存機構: `clifford_decomposition`
  (restriction 版), `CliffordSingleOrbit`, `card_mul_inner_self_induce_eq_card_inertia`,
  `apply_one_le_induce_apply_one_of_liesOver`。誘導版 decomposition producer は要 build (substantial)。
- coset-constancy assembly `psi_constant_on_xK` (S14:2959): horth[3 の全 χ_M 集約] + M data + psi_constant chain。
- witness coherence `sibleyTarget_frobI` (S14:1652, sorry) = (6.8) case-c1 Sibley target (別 deep piece)。

### loop⁶¹ (2026-07-01 lane-b resume³): critical-path 精査 — M-side は構成的 Clifford (issue 0026) に gated

(12.16) 原文 (§12 mmd) と (12.4) engine を精読し、(12.14)→(12.16) の残 gap を厳密特定:

**(12.14) 構造 (原文)**: `ψ=χ_L^{τ₁}` (L=witness, Frobenius by 12.10)。「By (5.5), ψ∈ℤ[R(χ)].
Thus, by (12.3) and (12.4), ψ is constant on xK」。⟹ **(5.5)[done loop⁶⁰] + (12.3) + (12.4)-applied-to-M**。
- **(12.4) engine は proven** (parameterized on `data`+`horth`): `orthogonal_character_constant_on_coset`
  (S14:1607) = `Sset_offKernel_vanishes_off_H` + kernel-part。horth 入力 = loop⁶⁰ の horth-combine。
- **∴ (12.14) の残 gap は (a) data_M (M の CharacterDecompositionData) + (b) `constituent_diff_support_subset_nonescaping`
  (S14:1274, sorry) の 2 つ**。両方とも **構成的 Clifford** に依存:
  - **data_M** = `typeI_induced_char_constituents` (M は非 Frobenius counterexample、12.8): (12.2.a) 分解
    `Ind_H^M θ=Σφ (mult-one)`。原文証明「follows from (8.2.c)+(1.7.c)」。**(1.7.c)** = [T=I_M(θ), T/H abelian,
    gcd(|H|,[T:H])=1 ⟹ Ind_H^M θ=Σχ_i (n=[T:H], mult-one, 次数 [M:T]θ(1))]。mult-one (e_φ=1) は
    **coprime ramification 理論** (θ が T へ extend、Gallagher/[Is 6.x]) 要 → 構成的 Clifford correspondence。
  - **constituent_diff_support_subset_nonescaping**: 原文「Res_H φ_i = Σ conjugates of θ (Clifford [Is 6.2]),
    ∴ Supp(φ_1-φ_2)⊂A(L)-H^#」。`data` field に無い **Res_H φ=Σ共役θ** (全構成要素で同一) を要 → 同じく Clifford。

**結論**: M-side (12.14) 全体が **構成的 Clifford correspondence (Isaacs 6.2/6.11 + Pf (1.7)) = issue 0026** に
gated。現状 `clifford_decomposition` は **conditional 形のみ** (Clifford data を外部供給、構成せず)、
`CliffordSingleOrbit` は LiesOver/次数境界のみ。**構成的 producer (Res の single-orbit core + inertia induction
bijection [Is 6.11] + cyclic/coprime mult-one [(1.7)]) は未在** = 大規模 shared infra build。
prereq (1.2)[S03b done], (1.5.a)[Clifford.lean 一部] は available。**次の genuine 上流 = issue 0026 (Clifford core)**
だが shared infra ゆえ claim-before-build (9000 issue) 対象。α レーン (§10-13 char) も要すると見込まれ、coordination point。

**L-side 別 gate**: witness coherence `sibleyTarget_frobI` (S14:1652, sorry) = (6.8) case-c1 Sibley target。
**重要: S08 は 0 sorry — (6.8) body `sibleySetup_is_coherent` は proven**。∴ 唯一の gap = Frobenius witness の
`SibleyDadeHypothesis` producer (現在 producer 無し、consumer のみ)。これは Clifford 非依存の tractable L-side
build で、landing すれば `frobenius_typeI_coherent` (12.6) → `witness_L_coherent` (S14:2458→2463 が `sibleyTarget_frobI`
経由 sorry) → witness の (5.5) 実適用が全て unconditional化。**高価値・次セッション最有力**。

**`sibleyTarget_frobI` 構成 route (turnkey)**: `SibleyTarget hyp.tau hyp.Sset hyp.A` を構成。
`SibleyDadeHypothesis` (S08_CoherenceCorePart1:3265) の 15 field:
- `H := hyp.H.subgroupOf L`, `W1 := C` (hfrob の complement)。
- `H_ne_bot`/`H_normal`/`H_nilpotent`/`split`(L=H⋊W1)/`W1_nontrivial`/`card_L_odd`: hyp+hfrob から直接。
- `dade`: **crux**。ambient `sharpImage (hyp.H.subgroupOf L)` は `typeIA L hyp.typeI` (=H^#) と命題的等号
  (`typeIA_eq_sharp` (S14:3289) + `sharpImage`=map∘subtype∘subgroupOf の計算; defeq でない)。
  **cleaner route = fresh 構成** `S04.of_isTISubset` (S04:267, `hA_sharp`/`hA_L`/`hL_norm`/`hTI` 入力) →
  `of_isTISubset_H` (S04:304) が `dade.H a=⊥` を自動供給 (= `dade_H_eq_bot` field)。TI 性は witness の
  A(L)=H^# TI (8.12.c/12.9) から。
- `tau_eq : sib.tau = hyp.tau`: 両者 TI Dade map (= Ind_L^G on supported lattice) ゆえ `IsDadeMap.unique`
  (S04:3645) で一致。要 hyp.dadeData.dade も TI map = `∀a, hyp.dadeData.dade.H a=⊥` (witness Frobenius ゆえ;
  `H_eq_supportKernel` + escaping 空)。`isDadeMap_induce_of_forall_H_eq_bot` (S14:1180) が両側を Ind に落とす。
- `S`/`S_eq`: hyp.Sset は既に {Ind_H^L θ|θ≠1} 形 (S14:85) ゆえ S_eq 直接。`A0_eq`: `supportInSubgroup (sharpImage H) L
  = hyp.A` を sharpImage=typeIA から congr。`cases := Or.inl hfrob`。`hconj`: hyp.hconj (ambient 一致下)。
推定 ~150-250 行 + 補助 (TI 性・forall_H_eq_bot・sharpImage=typeIA)。fresh-dade route が transport 回避で最善。

### 🛑 loop⁶² (2026-07-01 lane-b resume³): sibleyTarget_frobI は witness で unsound — loop⁶¹ plan 撤回

**上の loop⁶¹ plan は誤り** (「A(L)=H^# TI、escaping 空」は witness で偽)。構成中に発覚:

**Peterfalvi 原文三重確認**:
- **(6.8)(a)** (mmd 04.8:138): 「\(H^{\#}\) is a **TI-subset of \(G\)** with normalizer \(L\)」— (6.8) coherence の必須前提。
- **(12.10) proof** (mmd 04.14:59): witness L につき「**By (12.9), \(H^{\#}\) is not a TI-subset of \(G\)**」と明言。
  (12.9) の x∈Ω₁(P₀)^#⊆H^# は C_G(x)⊄L (escaping)。∴ `dade.H x = supportKernel L L H^# x
  = maxNilpotentNormalHall L ⊓ C_G(x) = H⊓C_G(x) ∋ x ≠ ⊥` (S14:1311-1314 の supportKernel 定義)。
- **(12.6) proof** (mmd 04.14:45): coherence は **3-case split** — (i) H^# TI ⟹ (6.8); (ii) Def(8.3) case(b)
  [H abelian rank 2] ⟹ 全 S 同次数 ⟹ (5.7); (iii) case(c) [|L/H|∣p-1] ⟹ (6.5.c)。witness は非TI = case(b)/(c)。

**帰結 — 現行 architecture の mis-modeling**:
- `SibleyDadeHypothesis.dade_H_eq_bot` (∀a∈H^#, dade.H a=⊥) = H^# TI in G を hardcode。
- `sibleyTarget_frobI` (cases:=Or.inl hfrob, (6.8)(c1) branch) は dade_H_eq_bot 必須 → **witness で数学的に unprovable**
  (dade.H x ≠ ⊥)。docstring 「Frobenius だから (6.8) SibleyTarget available」は overclaim ((6.8) は Frobenius に
  加え (a) TI も要求; witness は TI を欠く)。
- `frobenius_typeI_coherent` (12.6) は全 Frobenius L を sibleyTarget_frobI 経由にする → **TI case しかカバーせず**、
  非TI witness (case b/c) を取りこぼす。`witness_L_coherent`→`exists_witness_dadeNotation`→(12.16) capstone +
  (5.5) の witness 適用が全てこの unsound carrier に依存。

**正しい fix (設計分岐、要ユーザー判断)**: `frobenius_typeI_coherent` を `hyp.typeI.alternative`
(TypeIData の Def-8.3 3-way disjunction, MaximalSubgroupType:109) で case-split:
- case(a) TI: sibleyTarget_frobI (要 TI 仮説を signature に追加して honest 化) 経由 (6.8)。
- case(b) abelian rank 2: (5.7) 等次数 coherence (`S07_CoherenceConstantDegree` 在庫)。
- case(c) exponent∣p-1: (6.5.c) coherence (**在庫未確認 = 要 build の可能性**)。
残タスク: issue に記録。loop⁶⁰-⁶¹ で landing した補題 (centralizerSupport_sharp_eq_of_frobenius /
sharpImage_H_subgroupOf_eq_typeIA / transport 2 件) は**一般に正しく再利用可** (typeIA=H^# は真、transport も真)
— sibleyTarget_frobI の TI-case や case(b)/(c) build で使える。unsound なのは sibleyTarget_frobI の
「全 Frobenius で成立」claim のみ。

### loop⁶³ (2026-07-01 lane-b resume³): ✅ 3-case split 修正 landing + case b/c infra 課題特定

**ユーザー裁定 (2026-07-01)**: 設計分岐・想定違反は止まって聞かず **hub 裁定 9000-issue を立てて続行** ([[feedback-file-hub-issue-dont-stop]])。→ issue 9001 起票済、続行。

**landing (commit c774360d, build-green)**: `frobenius_typeI_coherent` を `hyp.typeI.alternative`
(Def8.3 trichotomy) で **3-case split** に是正。`sibleyTarget_frobI` は `_hTI` 仮説追加で TI-case 限定
(偽 claim 解消)。case(b)=`frobenius_typeI_coherent_of_abelianKernel` / case(c)=`..._of_cyclicQuotient`
を scoped lemma に分離。全 sorry が真の fillable statement に (従来の偽 sibleyTarget claim 解消)。

**case b/c の追加 infra 課題 (issue 9001 に追記)**:
- **case(c)** = (6.5.c) coherence producer、S07/S08 に在庫なし → 要 build。
- **case(b)** = `coherent_of_constant_degree` (S07:513) は `S07.Hypothesis(5.2)` の **global
  `IsIntegralIsometry`** を要求。witness Dade map hyp.tau は dim CF(L)>dim CF(G) ゆえ global 等長でない
  (IsCoherent が lattice-relative に weakened の理由と同じ)。⟹ **Dade-map ベースの等次数 coherence
  producer** (`isCoherent_pair_of_differenceImage` (S07:86) の n-member 一般化) が要る。
両者とも coherence infra の build 事項 = hub 9001 で claim 調整。次: case(b) の Dade 等次数 coherence を
`isCoherent_pair_of_differenceImage` + retarget family から一般化して build 試行 (最 tractable)。

### ✅ loop⁶⁴ (2026-07-02): HUB 裁定完了 — lane b が shared coherence/Clifford infra を build (unblock)

issue 9001 に **HUB 裁定** (2026-07-02 cron tick)。coordination-block 解消:
- **事項1 (3-case split unsound 是正)**: ✅ 承認・main 合流済 (`ed34cdc8`)。soundness 改善で非 regression と
  hub 認定 (unsound < honest sorry、CLAUDE.md doneness 原則合致)。今後も unsound→honest-scaffold 置換は非 regression。
- **事項2 (shared infra 割当)**: **3 件すべて lane b が claim-first で build** (policy 5B/6/7 + σ-theory 先例):
  - **(A') S07 (5.7) lattice-relative refactor** — turnkey (機械的: weakened (5.2) Hypothesis を
    commonImage/pairDecomp'/xFamily_inner に通す、coherentEqualDegree 無改造)。⚠ S07 既存 consumer
    (lane a coherence) を build-green 維持 (hypothesis 一般化ゆえ既存 caller 無影響のはず、full build で強制)。
  - **(A) (6.5.c) coherence producer** — 9000 番台で claim → build (shared leaf)。
  - **(B) 構成的 Clifford (issue 0026)** — 9000 番台で claim → build (0026 を subsume)。α は cite (dup 回避)。

**次セッションの優先 (unblocked、lane b assigned)**:
1. **(A') S07 lattice-relative refactor** が最優先 (turnkey・機械的・case(b) を直接 unblock、xFamily_inner_dade は
   その一部として既 landing)。weakened (5.2) Hypothesis を作り chain に通す → `coherent_of_constant_degree` の
   Dade-compatible 版 → `frobenius_typeI_coherent_of_abelianKernel` 埋め。S07 consumer は full build で green 検証。
2. **(6.5.c)** producer (case c) → `frobenius_typeI_coherent_of_cyclicQuotient` 埋め。→ witness coherence 完成。
3. **構成的 Clifford** (M-side、大規模) → `typeI_induced_char_constituents` 等。
これで witness_L_coherent → (12.13)/(12.14)/(12.16) の witness Dade 経路が全 unblock。

### ✅ loop⁶⁵ (2026-07-02 lane-b): (A') S07 lattice-relative refactor 完了 + case-b 着手

**(A') S07 refactor landing (commit `d31b9763`, full build green 3893 jobs)**: `S07.Hypothesis.tau_isometry`
(global `IsIntegralIsometry`) → 差-等長 `tau_isometry_diff` (`∀ a b c d ∈ S, ⟨τ(a−b),τ(c−d)⟩=⟨a−b,c−d⟩`)。
helper `inner_eq_on_zSpan_pair` (差-等長→zSpan 双線型拡張、`Submodule.mem_span_pair`+2-phase simp)、`pairDecomp`
に `hζ` 追加、`commonImage_inner_other` は直接 `tau_isometry_diff`、`xFamily_inner` を `hdiff` 版に (= S14
`xFamily_inner_dade` を subsume、後で dedup 可)、unused `tau_inner_eq` 削除。**`coherent_of_constant_degree`
が witness Dade map で使えるように**。S07.Hypothesis は未 construction ゆえ lane-a regression 皆無。

**case-b character-side helpers (commit `7c21ca08`)**: `Sset_hasNoRealCharacters` / `Sset_pairwiseOrthogonal`
を実証明 (既存 `frobenius_induce_char_singleton` 再利用)。⚠ **新 helper には `open scoped …S12.FiniteInduce in`
必須** (Fintype ↥L 供給; 無いと instance synth 失敗)。

**残: `frobenius_typeI_coherent_of_abelianKernel` (S14:1857, sorry) の埋め** = witness `Hypothesis L` から
`S07.Hypothesis hyp.Sset hyp.A` を構成 → `coherent_of_constant_degree` 呼び出し。field 別ソース (全 API 確認済):
- `tau := hyp.tau`; `conjugate_closed := Sset_closedUnderConjugate`; `no_real := Sset_hasNoRealCharacters`✓;
  `pairwise := Sset_pairwiseOrthogonal`✓。
- `tau_isometry_diff`: `dadeIntegralCharacterMap_inner_eq_on_supported_span` (S07:5344) + 差が `hyp.A`-supported。
  A0(dade)=typeIA、supportInSubgroup typeIA L = hyp.A。**差 supported は下記 `Sset_diff_supported` を作って共用**。
- `difference_image`: `dadeCharacterDifferenceImageOfDiff` (S07:5540, χ を `IrreducibleCharacter ↥L` 化 (=
  frobenius_induce_char_singleton の ξ) + ¬IsReal + `(χ̄−χ).support ⊆ supportInSubgroup typeIA L`)。
- `difference_images_orthogonal` (5.2.e): **最深**。`dadeIntegralCharacterMap_inner_conjDifference_eq_zero`
  (S07:5674) か `toOrthonormalImage_inner_eq_zero_across` 経由。要精査。
- `coherent_of_constant_degree` の hyp: `hSfin` (Sset 有限, θ-param), `hcard` (≥2: χ≠χ̄ 非実+conj閉), `hirr`
  (`inner_self_induce_eq_one_of_frobeniusGroup`), `hZIrr` (Dade supported diff→ZIrr, 要 infra 確認),
  `hconst`/`hdeg0` (等次数 [L:H]: `induce_apply_one`+`apply_one_eq_one_of_isMulCommutative`; ⚠ θ の群は
  `(typeF.H).subgroupOf L` — `_hab` の `IsMulCommutative ↥(typeF.H)` から subgroupOf に transfer 要
  `subgroupOfEquivOfLe` 等), `h1A` (1∉A: typeIA_eq_sharp), `hsuppdiff` (= `Sset_diff_supported`)。
- `hAH : ambientA = H\{1}` は `typeIA_eq_sharp` (S14:3289) から供給。
順序: 上流=character/degree facts (tractable) → Dade fields (tau_isometry_diff/difference_image) →
(5.2.e) difference_images_orthogonal (deep) → assembly。multi-turn 想定。

### ✅ loop⁶⁶ (2026-07-02 lane-b cont.): 12.6 case-b の hard core 完了 — witness S07.Hypothesis 全 field + coherent 主 hyp を実証明

`frobenius_typeI_coherent_of_abelianKernel` (S14, まだ sorry) 用の witness 事実を **10 named lemma** で
実証明 landing (全 build-green、7 commit)。**S07.Hypothesis hyp.Sset hyp.A の 7 field 全て + coherent_of_constant_degree
の主要 hyp が揃った**。ソース lemma (全て S14, `open scoped …FiniteInduce in` + 必要なら `open …S09.Cert in` 付):
- `Sset_isIrreducibleCharacter` (hfrob): 各 Ind θ 既約 (`isIrreducibleCharacter_induce_of_frobeniusGroup`)。
- `Sset_hasNoRealCharacters` (hodd, hfrob): no_real field。
- `Sset_pairwiseOrthogonal` (hodd, hfrob): pairwise field。
- `Sset_inner_self_eq_one` (hfrob): hirr (`inner_self_induce_eq_one_of_frobeniusGroup`)。
- `Sset_apply_one_eq_index` (hab): 等次数 [L:H] (hconst/hdeg0; `induce_apply_one`+`apply_one_eq_one_of_isMulCommutative`,
  `subgroupOf_isMulCommutative` instance)。
- `Sset_diff_supported` (hab, hAH): hsuppdiff + tau_isometry の supp (member vanish off H + 等次数 → H^# supp)。
- `Sset_tau_isometry_diff` (hab, hAH): tau_isometry_diff field (`dadeIntegralCharacterMap_inner_eq_on_supported_span`)。
- `Sset_tau_diff_mem_ZIrr` (hfrob, hab, hAH): hZIrr (`dadeIntegralCharacterMap_mem_ZIrr_of_supported`)。
- `Sset_differenceImage` (hodd, hfrob, hab, hAH): difference_image field (`dadeCharacterDifferenceImageOfDiff`)。
- `Sset_differenceImages_orthogonal` (hodd, hfrob, hab, hAH): (5.2.e) field — signedDiff→`Sset_tau_isometry_diff`
  で source `⟨φ−φ̄,χ−χ̄⟩` に落とし 4 項 orthogonality (φ̄≠χ,χ̄ は ⟨φ,χ⟩=⟨φ,χ̄⟩=0 から)。**最深、一発 green**。

**残 = assembly のみ** (`frobenius_typeI_coherent_of_abelianKernel` の sorry を置換):
```
obtain ⟨C, hfrob⟩ := _hfrob   -- kernel hyp.H.subgroupOf L =defeq (typeF.H).subgroupOf L
have hab := _hab.1
have hodd : Odd (Nat.card ↥L) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
have hAH : hyp.ambientA = (typeF.H : Set G)\{1} := by rw[Hypothesis.ambientA, hyp.typeIA_eq_sharp hG]; rfl -- sharpSubgroup=\{1}
refine ⟨(coherent_of_constant_degree ⟨hyp.tau, (fun _ _ _ _ ha hb hc hd => Sset_tau_isometry_diff …), Sset_closedUnderConjugate hyp, Sset_hasNoRealCharacters …, Sset_pairwiseOrthogonal …, (fun _ hχ => Sset_differenceImage …), (fun _ _ hφ hχ => Sset_differenceImages_orthogonal …)⟩ hSfin hcard (fun ζ hζ => Sset_inner_self_eq_one …) (fun a ha b hb => Sset_tau_diff_mem_ZIrr …) hconst hdeg0 h1A (fun a ha b hb => Sset_diff_supported …)).some⟩
```
の 4 finiteness hyp を埋める (infra 確認済):
- `h1A := one_not_mem_supportInSubgroup_sharp hyp.typeI.typeF.H hAH` (S09:744; hyp.A = supportInSubgroup ambientA L)。
- `hdeg0`: `Sset_apply_one_eq_index …` で index に、`Nat.cast_ne_zero.mpr (Subgroup.index_ne_zero_of_finite)` (mathlib Index:524)。
- `hconst`: `fun a ha b hb => by rw[Sset_apply_one_eq_index … ha, Sset_apply_one_eq_index … hb]`。
- `hSfin`: Sset ⊆ range(θ↦induce θ), `Set.finite_range` (要 `Finite (IrreducibleCharacter ↥H_sub)` = Finite.of_fintype/ofFinite)。
- **`hcard : 2 ≤ Sset.ncard`** (唯一の fiddly): ∃θ≠1 (H_sub nontrivial ← typeF.H_nontrivial + subgroupOf) → χ=induce θ,
  χ̄∈Sset (conj_closed), χ≠χ̄ (non-real) → `Set.one_lt_ncard`/{χ,χ̄}⊆Sset。∃θ≠1 は card(Irr)=card(ConjClasses)>1
  経由 (`card_irreducibleCharacter_eq`, CharacterCompleteness:558; nontrivial group の conjClasses>1 要確認)。
next: この assembly を書いて frobenius_typeI_coherent_of_abelianKernel を close → (12.6) case-b 完了。

### ✅✅ loop⁶⁷ (2026-07-02 lane-b): `frobenius_typeI_coherent_of_abelianKernel` PROVEN — (12.6) case (b) sorry-free

commit `9ba65c40`. **(12.6) case (b) 完全 discharge** — witness の abelian rank-2 kernel で S coherent。
assembly = 10 witness lemma (loop⁶⁶) から `S07.Hypothesis hyp.Sset hyp.A` を構成 + Dade-compatible
`coherent_of_constant_degree` (S07 refactor d31b9763) 呼び出し。残 finiteness hyp も discharge:
- `hSfin`: S ⊆ range(θ↦Ind θ)、`finite_irreducibleCharacter` で有限。
- `hcard`: nontrivial abelian kernel → ∃θ≠1 (`card_irreducibleCharacter_eq` + nontrivial ConjClasses
  via `mk_eq_mk_iff_isConj`/`isConj_one_left`) → {Ind θ, Ind θ̄} distinct non-real → `Set.ncard_pair`。
- `hdeg0`=`index_ne_zero_of_finite`, `h1A`=`one_not_mem_supportInSubgroup_sharp`。

**ハマり所 (次の同種 assembly で再利用)**:
1. **FiniteInduce instance diamond**: witness の Sset は `S12.FiniteInduce` scoped instance
   (`finiteSubFintype L` 等) で構築。assembly で `[Fintype ↥L]`/`[Invertible]` を signature に持つと
   別 instance になり `induce`/`τ` が Sset 要素と不一致。→ **frobenius_typeI_coherent chain (case b/c +
   hub) の explicit instance binder を全削除**し `[Finite G]` + `open scoped …FiniteInduce in` に統一
   (sibling `frobenius_typeI_induced_char_constituents` と同型)。
2. **`open scoped … in` は docstring の前**に置く (docstring と theorem の間だと構文エラー)。
3. **strict-implicit ⦃a b c d⦄ の field lambda**: `fun ha hb hc hd =>` は ⦃⦄ を食う → membership が
   ClassFunction 扱いに。`fun _ _ _ _ ha hb hc hd =>` と placeholder 要。
4. **`typeIA_eq_sharp` は forward ref** (typeI_frobenius 経由、後方定義) → `typeIA_eq_sharp_of_frobenius`
   (hfrob param 版) を case-b 前に切り出し、既存 typeIA_eq_sharp は dedup で cite。
5. **coherent_of_constant_degree は S07_CoherenceConstantDegree** — S14 に import 追加要。
6. **term-mode `rfl` の metavar/coercion**: Sset membership/range membership は `simp only [Sset,
   mem_setOf_eq]` unfold + `refine ⟨…, ?_⟩; rfl` (tactic) で。`θ.toClassFunction` が normal form。

**残 lane-b (issue 9001)**: (6.5.c) coherence producer (case c = `frobenius_typeI_coherent_of_cyclicQuotient`,
まだ sorry) + 構成的 Clifford (M-side)。case (c) は §6.5 汎用 coherence infra が要 (S07/S08 在庫なし)。

### ✅ loop⁶⁸ (2026-07-02 lane-b): (12.6) case (c) の全景マップ + (6.5.c) の 2 普遍 leaf を実証明

**(12.6) case (c) の教科書構造を確定** (mmd 04.14 L45 の (12.6) proof + 04.8 §6):
case (c) = Def(8.3)(c) (H^# **非 TI**, |L/H|∣p−1)。proof は **(6.5.c) 経由の矛盾**:
S 非可換 coherent と仮定 → (6.5.a) `six_three_index_bound` で |H:H'|≤4|L:H|²+1 + (6.5.b) H 非可換 p-群
→ (8.2.a)+(8.3.c) で |L/H|∣p−1 → (6.5.c) が |L:H|∤p−1 を主張 → 矛盾。∴ S coherent。

**commit `f612848a`: (6.5.c) に要る 2 普遍 leaf を S08_PGroupReduction に実証明 (axiom-clean, full 3894 green)**:
- `six_five_c_arith` (算術核): p 奇素数, d 奇, d∣p−1, p²≤HH', HH'≤4d²+1 ⟹ False。
- `sq_le_card_abelianization_of_isPGroup_of_noncomm`: 非可換有限 p-群 ⟹ p²≤|Abelianization P| (Burnside basis)。
  + helper `isCyclic_of_isPGroup_of_isCyclic_quotient_commutator` (P⧸⁅P,P⁆ 巡回⟹P巡回,
  `commutator_le_frattini_of_pgroup` (Isaacs Ch04) + `frattini_nongenerating`)。
これらは reduction がどの形でも消費する普遍事実。

**⚠ 判明した真の gap (次セッションの本丸)**: S08 の (6.5)/(6.8) 機構
(`isPGroup_of_not_coherent` c1・`abelianization_card_le_of_not_coherent_c2` c2 — 共に sorry-free で
(6.5.a) index 上界+p-群を ¬coherent から出す) は **すべて `SibleyDadeHypothesis` 上**。
`SibleyDadeHypothesis` は **`H_sharp_ti` (H^# TI) を必須 field に持つ** (CorePart1:3279)。
**case (c) は H^# 非 TI** (A=A(L)=`supportInSubgroup typeIA L`, τ=Dade rel A(L)) ゆえ witness
`Hypothesis L` は SibleyDade に直接該当せず。よって case (c) を閉じるには:
**(6.5) reduction (「¬coherent ⟹ index 上界」) を witness の A(L)-Dade setup へ一般化**する必要がある
(= `abelianization_card_le_of_not_coherent` の A=A(L) 版; six_two/six_three の τ を witness τ に張り替え)。
(6.8) full coherence (caseA/B) は要らない — case (c) は 2 leaf の矛盾で閉じるショートカットゆえ、
reduction (index 上界+p-群) だけ witness τ で出せれば `six_five_c_arith` + `sq_le_...noncomm` で終わる。

**次 (優先順)**: (A) witness `Hypothesis L` の (5.2)/(6.1)/(6.4) 充足を確認 (τ=dadeIntegralCharacterMap が
(5.2) を満たすか, S07.Hypothesis 経由で既知か) → (B) `six_two_index_bound`/`six_three` の witness-τ 版
(または general `six_three_descent` (S08_Theorem62_63_Standalone, (6.2) oracle `h62` 経由) を case-c の
irreducible-member 状況で discharge) → (C) `abelianization_card_le_of_not_coherent` witness 版 →
(D) case (c) assembly (H 非可換 = |L/H|>1 ∴ H'≠1; p 奇 = Odd p from odd order; 2 leaf 適用)。
multi-turn 想定。(6.2) oracle `h62` の irreducible-member discharge (`sMember_index_le_two_psi` 系) が
case-c で効くかが (B) の鍵 — case c は K=H が p-群ゆえ member Ind_H^L θ は既約 (θ≠1, Frobenius inertia=H)。

### ✅ loop⁶⁹ (2026-07-02 lane-b): (6.5.c) coherence engine を実証明 — case (c) を 3 obligation に集約

**commit `8df995ec`: `nonempty_coherent_SOf_bot_of_index_dvd` (S08_PGroupReduction, axiom-clean, full 3894 green)**。
発見: 抽象 S07 setup 上の `six_three_of_six_two_oracle` (S08_Theorem62_63_Standalone) が
(6.2)/(6.3) chain 全体を **(5.6) break-member oracle `h56`** に還元済 (τ 一般、SibleyDade 非依存)。
→ これに前 commit の 2 leaf (`six_five_c_arith` + `sq_le_card_abelianization_of_isPGroup_of_noncomm`)
を組み、(6.5.c) 結論「SOf ⊥ coherent」を出す engine を sorry-free で landing:
背理法 → oracle で |H:H'|≤4|L:H|²+1 (else coherence 矛盾) → 非可換 p-群で p²≤|H:H'| → arith 矛盾。

**engine の signature = case (c) の残 obligation を parameter 化** ([[feedback-gated-endpoint-skeleton-pattern]]):
`(hp: p 素数) (hHp: IsPGroup p H) (hnonab: H 非可換) (hodd_p) (hodd_LH) (hdvd: |L:H|∣p−1)`
`(hH'lt: ⁅H,H⁆<H) (hcoh: Coherent(SOf ⁅H,H⁆)) (h56: break-member oracle) → Coherent(SOf ⊥)`。

**残 (次セッション) = witness 供給の 3 件** (これで `frobenius_typeI_coherent_of_cyclicQuotient` を閉じる):
1. **SOf**: witness の S(A) filtration を定義 (`{Ind_H^L θ | θ∈Irr(H.subgroupOf L), θ≠1, A ⊆ ker θ}`;
   Sibley `SsubFiltration` を witness τ 用に。SOf ⊥ = hyp.Sset, SOf ⁅H,H⁆ = S(H'))。
2. **hcoh** = S(H') coherent: θ が H/H' 経由 (linear) ゆえ Ind 次数 = |L:H| 一定 → `coherent_of_constant_degree`
   (case b `frobenius_typeI_coherent_of_abelianKernel` の Sset lemma 群を subfamily に流用)。
3. **h56** = (5.6) break oracle: case c は K=H p-群 → member 既約 → Sibley `exists_coherentBreakPair` +
   (5.6) `coherentDegreeSqNormBound_of_not_coherentW` から組む (最深、multi-turn)。
+ 供給の付随: `hp/hHp` (H が p-群 = (6.5.b) reduction — chief factor 経由; または _hexp から), `hnonab`
   (¬coherent ⟹ 非 constant-degree ⟹ 非可換), `hdvd` (_hexp の (8.3.c) + (8.2.a) exp(L/H)=|L/H|)。
注意: H が p-群である事実 (6.5.b) は _hexp が直接与えない — chief-factor reduction が要る (未解決の追加 gap)。

### ✅ loop⁷⁰-⁷⁵ (2026-07-02 lane-b): hcoh 完成 + nilpotency — case (c) の残は h56 のみに集約

**loop⁷⁰-⁷⁴ で (6.5.c) engine の hcoh 引数 (S(H') coherent) を完全 landing** (全 axiom-clean):
- SOf (SsubFiltration + bot/subset/antitone) `b31979dc`。
- S(H') 等次数 (inflation で θ(1)=1) `1dbe96bb`。
- 部分族 S07.Hypothesis 7 field (diff_supported/tau_isometry/conjugate_closed/tau_diff_ZIrr/
  differenceImage/differenceImages_orthogonal; no_real/pairwise は subset で inline) `77ec8c1d`+`31024a16`。
  **鍵: case-b の field 群で hab が要るのは等次数 (x=1) のみ → S(H') では commutator-kernel lemma で代替。**
- `SsubFiltration_commutator_coherent` (hcoh 本体、coherent_of_constant_degree 呼び) `acdf9a79`。
- `typeF_H_subgroupOf_isNilpotent` ([IsNilpotent ↥K]、maxNilpotentNormalHall + 転送) `8993253a`。

**残 case (c) = h56 (最深) + それに従属する配線**:
- **h56 = (5.6) break-member bound over witness τ**。Sibley 版 `six_two_index_bound` (CorePart2:3750) =
  `exists_coherentBreakPair` (抽象、τ 一般で OK) + `sMember_index_le_two_psi` (CorePart2:3343、**SibleyDade
  固有の (5.6) 深部**)。h56 を witness で得るには **`sMember_index_le_two_psi` を抽象 τ/S/A0 へ一般化**する
  必要 (case c は K=H p-群ゆえ member 既約 = irreducible case、reducible の一般 oracle=issue 2022 より易しい
  はず)。これが最深の残タスク (2-3 iteration 想定、cross-lane (6.2) oracle と重なる可能性)。
- h56 が出れば: index 上界 (six_three_of_six_two_oracle 対偶) → IsPGroup
  (`isPGroup_of_isFrobeniusGroup_of_card_le`、card W₁=K.index bookkeeping 要) → hnonab (K abelian なら
  ⁅K,K⁆=⊥ ゆえ SOf⁅K,K⁆=SOf⊥、hcoh が hncoh 矛盾 → engine 内で導出可) → hdvd/hcyc (_hexp の (8.3.c)+(8.2.a))
  → engine + `SsubFiltration_bot` で Coherent(Sset)=goal。
- engine 改良案: hnonab/IsPGroup を engine 内部で導出 (Frobenius 構造を取る) すると配線が減る (未実施)。

**loop⁷⁶ h56 de-risking (重要)**: h56 chain を精査。**抽象 (5.6) core `coherentDegreeSqNormBound_of_not_coherentW`
(S08_CoherenceWeighted:635) は `S04.Hypothesis G A L` + `dadeIntegralCharacterMap hyp (fullDadeIsometryData
hconj)` 上 — これは witness τ の形そのもの** (`hyp.tau = dadeIntegralCharacterMap hyp.dadeData.dade
(fullDadeIsometryData hyp.hconj)`)。∴ **core は witness に直接適用可、根本 blocker なし**。h56 の作業 = core の
~20 仮説 (χmem 列挙・mc・Dmem 分解・orthogonality・tau1・a1 等) を witness 構造から供給 (Sibley
`sMember_degreeSumBound_of_not_coherent` (CorePart2:2912) をミラー) + wrapper 算術 (sMember_degreeSqReBound
→ sMember_index_le_two_psi → six_two_index_bound)。case c は member 既約ゆえ mc i=1 (‖·‖=1)、Dmem は
singleton 分解。Frobenius index=card は `IsComplement.card_right (isComplement'_def.mp hfrob.isComplement)`
の 1 行。次: witness `sMember_degreeSumBound` 版から bottom-up に build (core の仮説供給が本体)。

## loop⁷⁷–⁸⁹: (12.6) case (c) PROVEN (commit 4753cd14)

**`frobenius_typeI_coherent_of_cyclicQuotient` は sorry-free + axiom-clean** ([propext, Classical.choice,
Quot.sound])。(12.6) 3 case のうち (b)(loop⁶⁷ 9ba65c40)・(c) が完了。full assembly `frobenius_typeI_coherent`
の残 sorryAx は **case (a) `sibleyTarget_frobI` のみ** (→ (12.3) `nonconjugate_typeI_R_orthogonal` → (8.18.c)
`nonconjugate_diffImage_inner_zero` @ S14:665、§10 thickened-support 幾何)。

**達成した 2 部構成:**
1. **engine 強化** `S08.nonempty_coherent_SOf_bot_of_index_dvd`: (6.5.b) p-群還元を **engine 内部化**。
   旧 `{p}(hHp:IsPGroup p H)` 固定 → 新 `hF:IsFrobeniusGroup ↥L H C`+`hLodd`+`hdvd(∀p||H|)`。by_contra 内で
   (6.3) index bound → `isPGroup_of_isFrobeniusGroup_of_card_le hF … hbound` で p 生成 (`isPGroup_of_not_coherent`
   をミラー; bound は ¬coherent 文脈必須ゆえ engine 内でしか導出不可) → `six_five_c_arith`。oddness は |L| odd から。
2. **witness 配線** (S14): `rw ← SsubFiltration_bot` → K=(L_F).subgroupOf L の abelian 場合分け:
   - abelian: `⁅K,K⁆=⊥` (commutatorElement_eq_one_iff_commute) → `S(⁅K,K⁆)=S(⊥)=S`、hcoh で coherent。
   - non-abelian: engine + hcoh + hH'lt (K nilpotent not perfect) + h56=`Sset_six_two_index_bound`
     (lambda で `commutator(K/A)≠⊤` を `A≤⁅K,K⁆<K`+nilpotent から導出)。
   - **hdvd** (最大の山): odd Frobenius 補群 C は Z-群 (`S10.isZGroup_of_isFrobeniusGroup_of_odd`) → SZ 共役
     (`IsComplement'.exists_conj_of_coprime`) で `C≃U` → U も Z-群 → `K.index=[L:H]=|U|=exp(U)`
     (typeF.complement + `IsZGroup.exponent_eq_card`) → `_hexp` (8.3.c) が `K.index∣p−1` を与える。

**次の B レーン frontier (loop⁹⁰+):** **`witness_L_coherent` を sorry-free 化**。現状 witness_L_coherent (S14:~3958)
は `frobenius_typeI_coherent`(3 case) を呼ぶため case (a) の sorry を推移的に負う。だが **witness は case (a) を
取らない** (Peterfalvi (12.10): witness の H^# は non-TI)。∴ witness の `hyp.typeI.alternative` の hTI 枝を
(12.10) で排除できれば witness_L_coherent は (b)(c) 済みゆえ sorry-free になる → (12.16) Dade 計算の coherence
入力 `hB` が閉じる。要調査: witness Hypothesis が「H^# not TI」を carry するか (12.10 の所在)、hTI→False の導出。
これが (12.16)→(16) 最終矛盾への実質前進。case (a) の (8.18.c) 幾何本体 (S14:665) は general 12.7 用で FT witness 経路外。

## loop⁹⁰: (12.10) 非-TI で witness coherence を (8.18.c) から decouple (commit b04c306f)

`witness_L_coherent`・`witness_L_zeta_bound` を **(12.6) case (b)/(c) のみ**経由に変更 (3-case
`frobenius_typeI_coherent` を経由しない)。case (a) `sibleyTarget_frobI` は (8.18.c) §10 thickened-support
幾何を推移的に要するが、**witness は非-TI** (Pf (12.10)) ゆえ case (a) を取らない。
検証済: `_of_abelianKernel` (b)・`_of_cyclicQuotient` (c) 共 [propext, Classical.choice, Quot.sound] (axiom-clean)。
∴ `witness_L_coherent` の sorryAx source は now **(12.9)/(12.10)/(12.11) の genuine witness 事実のみ** で
(8.18.c) を含まない。

**新 `witness_H_sharp_not_isTISubset` ((12.10) 非-TI 節)**: reduction は**実証明** — `N_G(H)=L` を inline
(coatom L + simplicity で `N_G(L_F)=⊤` を排除、`maxNilpotentNormalHall_le{,_normalizer}`)、TI-failure は
`g ∈ C_G(x)∖L` が `x ∈ H^#` を中心化 (`gxg⁻¹=x`, `g∉N_G(H)=L`、`data.centralizer_x_not_le_L`) で witness。
唯一の残 `sorry` = 精密な (12.11)-gated 事実 `x ∈ H` (`x ∈ M⊓L ≤ L_F`)。

**次 frontier (loop⁹¹+, task 5)**: (12.11) `intersection_complement_structure` を証明 → hxH を fill
(x∈M は P0_le_M、x∈L は mainSubgroup≤L の 5-type case-split)。その後 witness path の残 genuine gap は
(12.10) `witness_L_frobenius`。doc-order 上流優先で (12.11)→(12.10)。

## loop⁹¹: §12 witness-path gate map (issue 9003) + hxH←(12.11) 配線 (commit c43881d4)

**調査結論**: β-lane の (12.6) coherence は完了。§12 下流は全て gated (issue 9003 が正本 map):
- **Cluster A (構造)**: (12.10) `witness_L_frobenius` [sorry] が linchpin、未形式化 §8-§11
  ((8.16)(8.6.a)(9.7.b)(10.10)(11.9.c)(11.6)) を要す。(12.11)(12.12)(hxH) は (12.10) に gated。
- **Cluster B (幾何)**: (8.18.c) `nonconjugate_diffImage_inner_zero` [sorry] → (12.3)→(12.14/15/16)。
  = `S10.support_mutual_exclusion` [S10:853, sorry] に gated。BG piece `conjClassSet_Mtilde_disjoint`
  は**証明済**、欠 bridge = A1↔M̃。

**次 β target (最高レバレッジ)** = `S10.support_mutual_exclusion`: BG disjoint piece 済ゆえ A1↔M̃
bridge assembly、(8.18.c)→(12.16) 全体を unblock。Cluster A は §8-§11 大 effort (§-owning lane 検討)。

**本 iter 概念的成果 (c43881d4)**: `mainSubgroup_le` (M_s ≤ M、ungated) 追加 + (12.11) を witness_H_sharp
の上へ移動 + `hxH` を実導出化 (x∈P₀≤M ∧ x∈P₀≤L_s≤L ⟹ x∈M⊓L≤L_F、(12.11) cite)。→
`witness_H_sharp_not_isTISubset` は body sorry-free ((12.10) 非-TI reduction 完全組立、唯一の sorry は
cite 先の (12.11) = Peterfalvi が置く場所)。

## loop⁹²: (8.18.c) 前提 `support_mutual_exclusion` を PROVE (commit 65a2be52, issue 9003 Cluster B)

`S10.support_mutual_exclusion` (Pf 8.18.c、S10_MinimalSimpleStructure:854) を sorry-free + axiom-clean 化。
**旧 statement は偽**だった (nonconjugacy 仮説なし → conjugate S=T で sharp set が相互 support)。必要な
`IsTypeI S/T` + `¬ IsConjugateSubgroup S T` を追加 (全て (8.18.c) caller `nonconjugate_diffImage_inner_zero`
の hyp1/hyp2 type-I + hnot_conj から供給可)。証明: type-I ⟹ A₁=M_σ^# (`A1_eq_sigmaSharp_of_typeI_or_II`)、
y∈A₁(S)⊆M̃(S)⊆𝒞_G(M̃(S))、片方向 support で y∈𝒞_G(M̃(T))、`conjClassSet_Mtilde_disjoint` (BG 14.5(b) 証明済)
で矛盾。`import S10_BGInterface` 追加 (cycle 無)。§10 (lane-d/f) file の false/sorried statement の fix。

**次 (loop⁹³, task 7)**: (8.18.c) `nonconjugate_diffImage_inner_zero` (S14:665) の assembly —
support_mutual_exclusion + Dade-image support (supp(τ(φ−φ̄))⊆𝒞_G(A(L))) + inner_eq_zero_of_disjoint_support。
Ã/A1/𝒞_G 対応注意 (mutual-support→conjClassSet-disjoint 形要)。→ (12.3)→(12.16) FT chain 閉じる。

## loop⁹³: (8.18.c) inner-vanishing reduction を PROVE (commit cec700a5)

`nonconjugate_diffImage_inner_zero` (8.18.c, S14:665) を bare sorry → **実 reduction 証明**化 (hub 指示通り
S14 のみ)。τ-image `τ_i(φ_i−φ̄_i)` は dadeSupport(L_i) 外で消える (`constituentDiff_support_subset` =
R1_diffsupp のミラー + `dadeIntegralCharacterMap_apply_of_support` + `map_eq_zero_of_not_mem_dadeSupport`)
→ supp ⊆ dadeSupport、nonconjugate で disjoint → `inner_eq_zero_of_disjoint_support`。唯一の残 sorry =
**`dadeSupport_disjoint_of_nonconjugate`** (§10 M̃ geometry: dadeSupport⊆𝒞_G(M̃)+conjClassSet_Mtilde_disjoint、
S14 到達不可)。→ (8.18.c)→(12.3)→(12.16) chain はこの 1 幾何事実 modulo で閉じた。

**次 (loop⁹⁴, task 8)**: `dadeSupport_disjoint_of_nonconjugate` を証明。M̃ 機構が S14 不到達ゆえ relocate to
S10 (hub 要調整、loop⁹² の S10 逸脱 flag への応答を確認) / S14 import / lane a 所有化 のいずれか。

## loop⁹⁵: dadeSupport ⊆ 𝒞_G(L_F) (Frobenius) を PROVE + M-side subtlety 発見 (commit この iter)

`dadeSupport_subset_conjClassSet_maxNilpotentNormalHall_of_frobenius` を証明 (Frobenius L で
dadeSupport⊆𝒞_G(L_F)): `dadeSupport=thickenedSupport L L typeIA` (dadeSupport_eq_thickenedSupport) +
`typeIA⊆L_F` (Frobenius centralizer_kernel_le を inline) + thickenedSupport_subset_conjClassSet。
supportKernel_le/thickenedSupport_subset を file 前方へ relocate (self-contained)。

**発見した subtlety (task 9)**: dadeSupport_disjoint は両 L に Frobenius を要すが、(12.3) call site
(coherent_extension_constituent_orthogonal_Rset_of_nonconjugate S14:1278) は Frobenius 無し。(12.16) で
witness L は Frobenius だが **M は非-Frobenius** (counterexample)。∴ subset lemma は L には効くが M には効かない。
要調査: (8.18.c) 実 statement が typeIA 両側か typeIA-L/A₁-M mixed か ((M_F)^#⊆M_F は Frobenius 不要ゆえ
M-side は無条件で 𝒞_G(M_F) に入る可能性); nonconjugate_diffImage が hyp2.tau=typeIA なのと (12.15) の ρ_M=A₁(M)
の整合。M-side を A₁-based general subset で証明できれば dadeSupport_disjoint 完成。M̃ は S14 到達可。

## loop⁹⁶: (8.18.c) 実 statement を source から解明 — mixed Ã₁/Ã 形 + A₁ resolution

> ⚠ 本節の tight-A₁ 案は反証済 (下記 loop⁹⁷/⁹⁸ 追記参照)。

Peterfalvi §8 mmd (04.10) を読了。**(8.18.c) = mixed 形**: `Ã₁(S)∩Ã(T)=∅ ∨ Ã₁(T)∩Ã(S)=∅`
(A₁=sharp support `(L_F)^#`、A=full `typeIA`)。(12.3) 証明 (04.14) は「(8.18.c) で Ã(L₁)∩Ã₁(L₂)=∅ と
仮定」= **片側 A₁-based**。

**核心 resolution (Frobenius 不要)**: constituent φ は Ind_{L_F}^L θ の成分ゆえ **(L_F)^# 上 supported**
(Ind は normal L_F 外で消える、`induce_eq_zero_of_not_mem_normal` @ InducedCharacter:336)。(L_F)^# = A₁ ⊆ L_F
は**無条件** (Frobenius 不要、sharpSubgroup⊆subgroup)。∴ τ-image を **tight Ã₁-based** にできれば
`Ã₁(L)⊆𝒞_G(L_F)` が両側で Frobenius 無しに成立 → mixed (8.18.c) で disjoint。

**残 crux (deep §4 Dade)**: tight Dade vanishing `τ(f)⊆Ã₁ for f⊆A₁`。tool = `Hypothesis.restrict`
(S04:3472、A₁⊆A へ datum 制限、mem_dadeSupport_iff 有)。要: (i) constituent の (L_F)^# support を
CharacterDecompositionData から tighten (φ≤chi=Ind、supp φ⊆L_F — supp φ⊆supp chi は非自明、要 Ind 構造);
(ii) restricted datum で tight τ-vanishing; (iii) mixed 形の disjointness 組立。dadeSupport⊆𝒞_G(L_F)
(Frobenius, 済) は L=witness 側で Ã=Ã₁ ゆえ再利用可。

**評価**: (8.18.c)/dadeSupport は genuine deep §4/§8/§10 Dade-support 理論。loop⁹²-⁹⁶ で実 piece
(support_mutual_exclusion, reduction, dadeSupport⊆𝒞_G(L_F)) を landing したが完成は §4 restrict 深部を要す
multi-iteration。β-lane の cleanly-ownable coherence work は完了済。

## loop⁹⁷/⁹⁸ catch-up (2026-07-02 hub 追記): tight-A₁ 案は反証済・現 frontier 訂正

- **(i) loop⁹⁶ の「核心 resolution (Frobenius 不要、tight A₁ 形)」段落は反証済み**。loop⁹⁷ (33aa8553) で
  tight A₁ 形 (`diffImage_support_subset_conjClassSet_sigmaSharp`) を実装 → **loop⁹⁸ (7c40c3c2) で FALSE と
  判明し revert**: constituent は full `A = typeIA` 台であり、対称 A₁-only 論法は (12.15) の非-Frobenius `N`
  caller で偽。真の obligation = **mixed asymmetric `Ã₁(L₁) ∩ Ã(L₂) = ∅`** (spec =
  S14_MaximalI.lean:763-776 の docstring)。
- **(ii) loop⁹³ の「reduction PROVEN + 残 = `dadeSupport_disjoint_of_nonconjugate`」も無効** — 当該 decl は
  削除済。現状は `nonconjugate_diffImage_inner_zero` が bare honest sorry (S14:777、sorry @ :787)。
- **(iii) (12.10)**: `witness_L_frobenius` は sorry-free assembly 化 (S14:4097)。残 =
  `witness_L_isTypeI` (S14:4075) / `witness_L_complement_isZGroup` (S14:4086) の 2 pin (hub 9003 Cluster A)。
- **(iv) §8 support theory**: issue 0096 carve-out により S10 内の Dade-support 宣言群
  (typeII_A_sets_TI/normalizer・dadeSupportHypotheses_typeI/typeP・support_mutual_exclusion) は
  **lane b が S10 内で build** (9003 裁定)。

## loop⁹⁹ (2026-07-02/03): §8 support theory 正面 build — (8.15) soundness fix + (8.17.c) axiom-clean + (8.18.c) + (12.3) Step A

issue 0096 裁定の §8 build を実施、5 commits (5807febb / 232aaf18 / 6d384805 / 97cbd6fe / dd82f094)。
経緯・詳細は issue 9003「lane b 進捗 loop⁹⁹」節が正本。要点:

- **(8.15) carrier が unfaithful pin で uninhabited だった** (escaping a で `H(a)=C_{M_F}(a)∋a` が
  (2.2.b/c) と矛盾、8021 と同根) → per-x `ftSupportKernel` (escaping ↦ BG `FT_signalizer`) に修正、
  `dadeSupport_eq_ftThickenedSupport` は proven lemma 化、`hconj` field 化。S12_Core/S14 追従。
- **(8.15) type-I 実証明** (`dadeSupportHypothesisData_of_subset` 汎用 assembly; A(M)+A₁(M))。
  pins: `typeIA_isConj_conj_in_M` (8.13.a) / `escaping_typeIA_signalizer_structure` (8.13.c1c2) /
  `FT_signalizer_conj_smul_of_escaping` (8.14 equivariance)。
- **(8.17.c)** `ftThickenedSupport_A1_disjoint_of_nonconjugate` **axiom-clean** (choice 同定は
  proven 済 BG lemmas で closing; escape→1<|𝓜σ| は `centralizer_le_of_maximalSigma_le_one`)。
- **(8.18.c)** `ftThickenedSupport_mixed_disjoint_of_nonconjugate` (type-I pair、(8.18.a/b/c)
  assembly 実証明 + π-part 冪 `mem_zpowers_mul_right_of_coprime`)。pins:
  `escaping_typeIA_mem_A1` (8.13.b) / `typeI_centralizer_le_and_unique` (8.12.b) /
  `supported_sigma_coprime` (8.13.c2c4)。
- **(12.3) Step A** (S14): `Sset_diff_support_subset_A1` → (2.11) restriction →
  `Sset_diff_tau_support_subset_ftThickenedA1`; constituent 版; mixed disjunction;
  `constituent_fullDiff_inner_zero_of_disjoint`。全 sorry-free。

**次 (loop¹⁰⁰) = bar-trick descent** で `nonconjugate_diffImage_inner_zero` (S14:897) を閉じる。
設計 (9003 に精密版): (i) τ conj-equivariance → CDI `ν=μ̄` → `conj X = −X`; (ii) integrality
(δ-展開) で `⟨α,X⟩=0`; (iii) S(χ₂) 内 R₁ pairwise distinctness で per-φ₂ 消滅; member-wise 化は
`toOrthonormalImage_inner_eq_zero_across` (existing)。要調査: τ conj-equivariance の既存 lemma
(IntegralCharacterMap level?)、⟨irr, ℤ[Irr]⟩ integrality API、R1cdi same-χ distinctness。

## loop¹⁰⁰ (2026-07-03): (12.3) bar-trick descent 完成 — `nonconjugate_diffImage_inner_zero` 実証明

commit f8ecb4a5。詳細 = issue 9003「lane b 進捗 loop¹⁰⁰」節が正本。要点:

- **descent core `constituent_diffImage_inner_zero_of_disjoint` は axiom-clean**。構成:
  `X = (χ₂−χ̄₂)^{τ₂} ∈ ℤ[Irr G]`、(8.18.c) disjoint 側で `⟨sd₁, X⟩ = 0` →
  (5.9.b) `ν₁ = μ̄₁` (`S07.CharacterDifferenceImage.nu_eq_mu_conj`、新規) + `X̄ = −X`
  (`tau_conj_of_supported` ← 既存 Galois 可換) + 整数 Fourier 係数 (`mem_ZIrr_inner_int` +
  新規 `ZIrrFourier.inner_conj_conj`) → `⟨μ₁, X⟩ = 0` → block cross-orthogonality
  (`constituentDiff_tau_inner_eq_zero_of_ne`、新 field `conj_not_mem` 使用) で per-φ₂ 化。
- **`CharacterDecompositionData.conj_not_mem` field 追加** ((12.2.b)): Frobenius producer 実証明、
  一般 producer は (8.2.c) obligation に conclusion 追加 (S14 唯一の support sorry のまま)。
- `nonconjugate_diffImage_inner_zero` は `hG` を取る signature に変更 (caller は
  `nonconjugate_typeI_R_orthogonal` のみ、`_hG` を活性化)。
- (12.3) の残 transitive sorryAx = S10_MinimalSimpleStructure の §8 pins 6 本 + (8.2.c)。
  **次 = loop¹⁰¹: §8/§16 pins 正面 build** (0096 carve-out、文書順 (8.12.b)→(8.13)→(8.14))。

## (2026-07-09, lane-b): (12.11) 第2主張 `intersection_le_kernel` — 10-step 分解 + steps 3-5 の reusable infra landed

Pf (12.11) 第2主張 `M ∩ L ≤ L_F` (S14:5245、b-owned、on-path 12.11→12.17) の deep proof に着手。
原文の議論を **10 step に分解**し、うち **Frobenius sub-structure + Wielandt (9.1) 部分 (steps 3-5) を
reusable infra として landed** (green)。

### 原文 (Pf 12.11 2nd, 04.14) の議論
A ≤ M∩L で |A| prime to |H|=|L_F| を取る。H nilpotent ゆえ P₀ ⊆ O_p(H)、A normalizes P₀=O_p(H)∩M。
(8.1.c) で P₀ は K=M_F を非中心化、(12.10) で A≠1 なら P₀A Frobenius kernel P₀。(9.1) を P₀A ↷ K に
適用 → C_K(A)≠1。(12.9) で C_K(x)≠1。(8.1.b) で A,x は M∩L の可換部分群に入る → A centralizes x →
A=1 → M∩L ⊆ H。

### 10-step 分解 (formalization)
1. A ≤ M∩L, |A| coprime to |H| (仮説として per-A に取る)。
2. P₀=O_p(H)∩M ⊴ L (O_p(H) char in H ⊴ L)、A ≤ M normalizes P₀。P₀ ≤ H。
3. **P₀A Frobenius kernel P₀** ← step 1 infra ✅
4. **P₀ が K を非中心化** ← C_M(K)⊆K (self-centralizing kernel) + p∤|K| (P₀ p-group nontrivial)。要 build。
5. **Wielandt (9.1) 対偶: C_K(A)≠1** ← engine infra ✅
6. C_K(x)≠1 ← (12.9) `CKx_not_le_Kprime` (C_K(x)⊄K' ⟹ ≠1)。容易。
7. (8.1.b): A ≤ U1 (C_K(A)≠1 経由) ∧ x ∈ U1 (C_K(x)≠1 経由)、U1=`TypeFData.U1` 可換。**要: A,x を complement U に conjugate で入れる** (Hall 論法、subtle)。
8. A,x ∈ U1 可換 ⟹ A centralizes x。
9. A ⊆ C_L(x) ⊆ H (L Frobenius 条件(4) `centralizer_kernel_le`) ∧ A⊓H=1 (coprime) ⟹ A=1。
10. **Reduction**: 全 π(H)'-A trivial ⟹ M∩L は π(H)-group ⟹ M∩L ⊆ H (H = Frobenius L の normal Hall)。要 build。

**coprimality gcd(|P₀A|,|K|)=1** (step 5 の Wielandt に必須): gcd(|P₀|,|K|)=1 は p∤|K| (ctr `p_dvd_index`+Hall、
S14:4749 で proven)。gcd(|A|,|K|)=1 は **first assertion `intersection_complements_K` (M∩L complements K) +
M_F Hall 性** から (∴ 第2主張は第1主張に transitively 依存; 第1は 8.13.c1/lane-a gated だが signature 正で cite 可)。

### landed (reusable infra、green)
- `IsFrobeniusGroup.frobeniusGroup_sup_of_invariant_le_kernel` (CoprimeAction.lean): internal 形。
  Frobenius L kernel N、P≤N nontrivial、Q⊓N=⊥ nontrivial が P を normalize ⟹ `IsFrobeniusGroup ↥(P⊔Q)
  (P.subgroupOf) (Q.subgroupOf)`。`centralizer_inf_kernel_eq_bot_of_not_mem` で conj_frobenius。
- `..._ambient` (CoprimeAction.lean): ambient-G 形 (P,A:Subgroup G、L の Frobenius は `↥Lsub`)。engine が
  subgroupOf transfer 無しで consume 可能。engine の lifting パターンを mirror。
- `exists_ne_one_centralized_by_complement_of_kernel_not_centralizes` (WielandtFixedPoint.lean): **steps 3-5
  を統合**。ambient step1 で P⊔A Frobenius 構成 → `frobenius_kernel_centralizes_of_complement_fpf` (既存 9.1
  第1特殊ケース ambient 版) の対偶で「P が K 非中心化 ⟹ ∃1≠n∈K, A が n を中心化」(= C_K(A)≠1)。ungated
  (coprimality・non-central は仮説供給)。

### step 4 landed (2026-07-09、green)
- `P0_not_le_centralizer_K` (S14): ¬ P₀ ≤ C_G(K)。route = BG Prop 10.11(b)
  `rank_centralizer_Msigma_inf_le_one` (P₀ σ(M)ᶜ-subgroup ゆえ rank(C(M_σ)⊓P₀)≤1) vs
  `two_le_rank_of_noncyclic_pSubgroup` (P₀ noncyclic ゆえ rank≥2) の矛盾。当初想定の
  self-centralizing (C_M(M_F)≤M_F) は不要 (rank 論法が clean)。
- helper (additive、reusable counterexample facts): `MF_eq_Msigma` (K=M_F=M_σ, Prop 16.1 f) /
  `p_not_mem_sigma` (p∉σ(M))。

### step 10 core landed (2026-07-09、green)
- `le_of_coprime_card_index_of_normal` (Mathlib/Subgroup.lean): H⊴G + gcd(|S|,[G:H])=1 ⟹ S≤H
  (general reusable、SH/H↪G/H の order が |S| と [G:H] を割る→coprime で自明)。step10 の reduction core。

### step 7 transfer landed (2026-07-09、green)
- `exists_abelian_centralizer_le_of_isComplement` (S14): typeF:TypeFData M + V が K=M_F の complement in M
  ⟹ ∃W abelian ≤ V, ∀y∈K#, V⊓C(y)≤W。**最も難しかった keystone** (共役 heavy ~55 行、3 iteration で landing)。
  proof: `IsComplement'.exists_conj_of_coprime` で U→V の SZ 元 m∈K を取り、W=U1.map(conj m)、
  bridge (map M.subtype + `map_subgroupOf_eq_of_le` + hom-eq)、containment (v=conj m u, u∈U⊓C(m⁻¹ym)≤U1)。
  **洞察**: M∩L 自体が K の complement (第1主張) ゆえ A も x(∈P₀⊆M∩L) も M∩L=V に居り共通 W に入る。

### 残 (次 iteration、最終 assembly = M-specific gluing のみ、hard math は全て landed)
landed 済 reusable infra: step1-5 (C_K(A)≠1 engine) / step4 (P₀ 非中心化 K) / step7 (共通 abelian W) /
step10 (Hall reduction)。残るは **wiring + M-specific 依存**:
- **P₀ ⊆ L_F**: `data.P0_le_Ls` (P₀⊆mainSubgroup L data.L_type) + `data.L_type = .I` (type 一意性、要確認) で
  mainSubgroup=M_F → P₀⊆L_F。**要**: L_type=I lemma or type uniqueness。
- **P₀' = O_p(L_F)∩M 機構** (infra=`opiCoreInG {p} (maxNilpotentNormalHall L)`, SubgroupInAmbient.lean):
  Pf は P₀=O_p(H)∩M と再定義 (A-invariant)。`le_normalizer_opiCoreInG_of_le_normalizer` で
  A≤normalizer(L_F)→A≤normalizer(O_p(L_F))、`opiCoreInG_le` で O_p(L_F)⊆L_F。`isPGroup_opiCoreInG_singleton`
  で p-group。**要 sub-lemma**: ctr.P0⊆O_p(L_F) (nilpotent L_F の Sylow-p 一意性; mathlib `IsNilpotent`
  Sylow normal) → ctr.P0⊆P₀'=O_p(L_F)∩M ゆえ P₀'≠⊥ ∧ step4 非中心化継承。
- **coprimality gcd(|P₀'A|,|K|)=1**: P₀'A≤M∩L complements K (第1主張) → |M∩L| coprime |K| (M_F Hall) → 継承。
- **per-A core** (A≤M∩L, A⊓L_F=⊥, A≠⊥ → False): `exists_ne_one_centralized_by_complement_of_kernel_not_centralizes`
  (P₀',A,K,L_F,L で C_K(A)≠1) → C_K(x)≠1 (12.9 `CKx_not_le_Kprime`) → step7 (V=M∩L で A,x∈W abelian ⟹
  A centralizes x) → step9 (`centralizer_kernel_le` で A≤C_L(x)⊆L_F、A⊓L_F=⊥ → A=1) 矛盾。
- **reduction** (step10): core → `Coprime (card(M∩L)) [L:L_F]` (q|both なら Sylow-q=nontrivial π(H)'-A で矛盾) →
  `le_of_coprime_card_index_of_normal` (↥L, (L_F).subgroupOf L 正規, (M∩L).subgroupOf L) → M∩L⊆L_F。
- Frobenius L = `witness_L_frobenius` (available、TypeIFrobeniusData)。
