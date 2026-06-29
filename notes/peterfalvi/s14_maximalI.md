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
