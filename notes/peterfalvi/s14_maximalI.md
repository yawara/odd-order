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
- **gate (remaining)**: only the `T = Ω₁(Z(O_p(H)))` **construction** (`|T|∈{p,p²}` from (12.9)
  rank 2; `E` normalizes & acts FPF on `T` from (12.10) Frobenius) + the `p+1` refinement (`A=1` via
  (12.11)/(12.9)) — these consume **(12.10)/(12.11)** [char/§8-gated, lane-b] and the intricate
  `O_p/Z/Ω₁` p-group structure.  ⟹ `complement_cyclic_order_dvd` (full disjunction) stays gated;
  the **rep-theory + conjugation bridge is the ungated reusable part and is now COMPLETE**
  (`E`-FPF-on-elem-ab-rank≤2 ⟹ cyclic+order, the subgroup form, sorry-free).  Wiring (12.12) to
  consume the bridge is "保険 skeleton" over a genuinely-blocked upstream ((12.10)) — defer per
  ft_path_policy until (12.10) lands or by hub decision.

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
