# Peterfalvi §3: Preliminary Results from Character Theory — mini-roadmap

**スコープ**: Peterfalvi §3 (pp. 5-9), mmd `04.3_pp_5_9_*.mmd` (140 行), 10 結果 ((1.1)-(1.10)).
形式化先 (予定): `OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean`.
ROADMAP 上の位置: **Phase 2b 第 1 波** (Phase 1 Isaacs Ch.指標論完成 + mathlib `Character.lean` API 確認後).
役割: **Phase 2b の入口**: mathlib `RepresentationTheory.Character` API と odd-order 特化結果の橋渡し.

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](../meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md).

- **§3 は dependency-graph leaf**: 内部 self-cite **2 件のみ** ((1.1)→(1.5.e), (1.5.a)→(1.6.a)). 既存「structured」評価は overstate; flat checklist が実態.
- **内部 hub 訂正**: 既存「(1.4) hub」→ 実は **(1.6) が forward 最多 (7 cites)**. (1.4) は §4 prereq として重要だが overall は (1.6) が上位.
- L18, L72 (1.5)/(1.7) "mid (Clifford)" → **low** (Clifford theorem は mathlib 不在, 新規 `Clifford.lean` 要; BG §2 Prop 2.2 と共有 module).
- L76 [Is] Lem 7.7 "(1.4) context" → **誤り**, 実は **§8 (Coherence) L150**.
- L25 (1.8) "◯ §14-§15" → 実は **forward 0 explicit cite** (background tool only).
- L20 (1.3) "mid Frobenius API" → 実は **partial low** (mathlib `indResAdjunction_homEquiv` categorical のみ; character-level numerical Frobenius reciprocity 不在).
- (1.5)/(1.7)/(1.8) bucket: 全て **(c) new helper 要** (既存「mid」誤認). 各 [Is] cite (Thm 6.32, 6.5, 6.11, Lem 2.21, Cor 6.28, Cor 2.30, Lem 3.2/Cor 3.5, Lang Ch.VIII Thm 3.1 = 計 8 件) は **全 proof body cite**, mathlib v4.29.1 で対応**ゼロ**, 全て新規 helper 要.
- 行数 "350-400 LOC" → **~1000-1200 LOC** (Wave 1a infra `ClassFunction.lean`, `InducedCharacter.lean`, `Clifford.lean`, `Inertia.lean`, `BrauerPermutation.lean`, `IsReal.lean`, `SchurCenterBound.lean`, `IsometryDifferencePair.lean`, `SecondOrthogonality.lean` 合計 ~600 LOC 含む).
- [BG] cite **0**: §3 mmd で [BG] 引用なし. 既存 "[BG] §1 軽" 等の言及は overstated.

## TL;DR — Phase 2b の入口, mathlib との橋渡し

Peterfalvi §3 は **Isaacs [Is] 1976 Character Theory Ch.1-7 と Peterfalvi 独自の odd-order strengthening の集約**. §3 の大半 ((1.1), (1.5)-(1.8)) は Isaacs の character-theoretic 再述 + odd-order 強化で、**mathlib 既存 API で薄くラップ可能**. ただし **(1.3) (Fourier 展開) と (1.4) (tau isometry)** は **§4 (Dade isometry) の基礎となる新概念** で、Phase 2b 形式化の最初の山場.

**形式化方針**: Phase 1 で Isaacs Ch.指標論 (Thm 6.32, 6.5, 6.11, Lem 2.21, Cor 6.28, Cor 2.30 等) が完成していれば、§3 の (1.1), (1.5)-(1.8) は薄い wrapper で完了 (合計 200 行程度). (1.3)-(1.4) は新規実装 (合計 130 行). §3 全体で約 400 行の Lean.

## §3 全 10 結果

| # | mmd 行 | 種別 | 主張要約 | Isaacs [Is] 対応 | mathlib | §4-§16 被引用 |
|---|--------|------|----------|------------------|---------|---------------|
| **(1.1)** | 5-7 | Characterization | `\|G\| odd ⇒ χ ≠ χ̄ for nontrivial χ ∈ Irr(G)` | **Thm 6.32** (real irreducibles ↔ real conjugacy classes) | low (odd-order specific) | ◯ §4-§6 (Dade hypotheses) |
| **(1.2)** | 9-15 | Vanishing | `H ◁ G, χ ∈ Irr(G), H ⊄ Ker χ, C_H(g)=1 ⇒ χ(g)=0` | **Thm 6.32** + 2nd orthog. relation | mid (orthog. API exists) | ◯ §11 (type analysis) |
| **(1.3)** | 17-37 | Basis + Fourier | `CF(H,A) basis → Ind_H^G ψ_j = Σ_i(ψ_j,χ_i) μ_i` (Frobenius reciprocity form) | **Frobenius reciprocity** (implicit in [Is] 6.15-6.16) | mid (Frobenius API 部分) | ☆☆ §4 (core), §7-§8 (coherence) |
| **(1.4)** | 39-45 | **Tau Isometry** | `τ: Z[X,H^#] → Z[Irr G], isometry ⇒ ∃ μ_i ∈ Irr(G), ε=±1: (χ_i - χ_1)^τ = ε(μ_i - μ_1)` | (Character orthogonality implicit, 新規補題) | **low** (完全新規) | **☆☆☆ §4 (2.4) prerequisite** |
| **(1.5)** | 47-69 | Clifford theory (5 部) | (a) Clifford decomposition (b) `\|χ\|²=r` 既約性 criterion (c) inertia-orbit (d) χ(1) 公式 (e) odd ⇒ χ̄ ⊥ χ | **Thm 6.5** (Clifford), **Thm 6.11** (induced from inertia), **Cor 6.28** | **low** (audit 訂正; Clifford 完全不在) | ◯◯ §5-§7 core setup; (1.6) が外部最多 hub |
| **(1.6)** | 71-83 | Kernel + descent (2 部) | (a) A ⊆ Ker(θ) ⇔ A ⊆ Ker(Ind_H^G θ) (b) quotient descent | **Lem 2.21** (kernel under induction) | mid | ☆ **forward 7 cite (§3 最多 hub)** §8×3, §11×3, §15 |
| **(1.7)** | 85-97 | Inertia decomp (3 部) | Ind_H^T θ = Σ e_i ψ_i, cyclic T/H ⇒ e=1 multiplicity-one | **Thm 6.11** + **Cor 6.28** + **Thm 6.5** | **low** (audit 訂正; Inertia/Clifford 不在) | 内部利用のみ (explicit 0) |
| **(1.8)** | 99-105 | Height bound | `ψ(1) ≤ \|G\|/√(\|C\|\|D\|)` (D/B ⊂ Z(C/B)) | **Cor 2.30** (Schur degree bound) | low | 0 explicit (audit 訂正); background tool only |
| **(1.9)** | 107-127 | Galois auto (2 部) | (a) Aut(Q_n) ⊇ Aut(Q_a) × Aut(Q_b), (b) χ^v(g) = χ(g^k) for ord(g)|a | **[L] Ch.VIII Thm 3.1** (cyclotomic auto) | low (cyclotomic) | ◯ §16 |
| **(1.10)** | 129-140 | Modular arith (2 部) | (a) χ(xy) ≡ χ(y) mod (1-ε), (b) (1-ε)|n in Z[ζ_p] ⇒ p|n | **Lem 3.2, Cor 3.5** (cyclotomic int) | low (cyclotomic) | ◯ §16 |

**FT 経路上の役割凡例**: ☆☆☆ critical (§4 prerequisite), ☆☆ core (§4 + §7-§8 主要), ◯ 標準利用.

## 主要結果の詳細

### (1.1) Odd Order ⇒ Real Irreducibles Distinguished

**主張**: |G| odd, χ ∈ Irr(G), χ ≠ 1_G ⇒ χ̄ ≠ χ.

**証明概要**: Z/2Z 作用を共役と指標共役で連動 → [Is] Thm 6.32 で「real irreducible 個数 = real conjugacy class 個数」. odd order では C^{-1} = C は C = {1} のみ (g^{-1} = g^x ⇒ x^2 ∈ C_G(g), odd order ⇒ x ∈ ⟨x^2⟩ ⊆ C_G(g), so g^{-1} = g, g = 1). 結論: real irreducible は trivial のみ.

**Isaacs 依存**: [Is] Thm 6.32 (Phase 1 Ch.6 で完成想定).

**mathlib**: 
- `Mathlib/RepresentationTheory/Character.lean` に `Character.innerProductDef`
- `Character.isReal` predicate (χ = conj χ) は未明示, 要追加
- Z/2Z 作用は手動定義

**形式化**: ~15 行 (Phase 1 Thm 6.32 + character conjugation).

**Lean status (2026-05-26)**:
- `OddOrder.RepresentationTheory.RealIrreducibleCharacter G` names the subtype
  `{χ ∈ Irr(G) | χ̄ = χ}`.
- `OddOrder.RepresentationTheory.card_realIrreducibleCharacters_eq_one_of_odd_card`
  records the conditional Brauer-permutation cardinal form of (1.1):
  `Nat.card (RealIrreducibleCharacter G) = 1` for odd `Nat.card G`.
- `trivialClassFunction`, `trivialIrreducibleCharacter`, and
  `trivialRealIrreducibleCharacter` now name the trivial character at the
  class-function / irreducible / real-irreducible levels.
- `OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card`
  records the corresponding pointwise form (`χ ≠ 1_G → χ̄ ≠ χ`).  As with the
  cardinal form, its proof depends on the routed Brauer permutation lemma
  proof core.
- `OddOrder.Peterfalvi.S03.characterDegree`, `SameDegreeFamily`, and
  `HasUniformDegree` name the degree conditions used by (1.4), (1.5), and
  §7 (5.7).
- Basic set and degree helpers are available without unfolding:
  `ClosedUnderConjugate.conj_mem`, `ClosedUnderConjugate.conj_mem_iff`,
  `HasNoRealCharacters.mono`, `HasNoRealCharacters.not_mem_of_isReal`,
  `SameDegreeFamily.eq`, `sameDegreeFamily_const`,
  `sameDegreeFamily_of_characterDegree_eq`, `HasUniformDegree.eq_of_mem`,
  `HasUniformDegree.mono`, `hasUniformDegree_empty`, and
  `hasUniformDegree_singleton`.
- (2026-05-30) `exists_natDegree_characterDegree_dvd_card` — **Isaacs Thm 3.11
  / Peterfalvi §6.7 degree datum** through the Peterfalvi `characterDegree` API:
  for `χ : IrreducibleCharacter G` (`[Finite G]`) there is `n : ℕ` with `0 < n`,
  `characterDegree χ = (n : ℂ)`, and `n ∣ |G|`.  This is the consumer-facing form
  of the integrality theory — it carries the `IsIrreducibleCharacter`/`ClassFunction`
  bridge `exists_natDegree_charValue_one_dvd_card` (= `finrank_dvd_card` through
  `φ 1`) onto Peterfalvi's `characterDegree`, since `characterDegree χ = χ 1`
  definitionally.  Lets `χ(1) ∣ |G|` flow into §6.7/§7 degree statements phrased
  through `characterDegree`.
- (2026-06-04) `exists_natDegree_characterDegree_eq_prime_pow_of_isPGroup` —
  **Isaacs Cor. 3.12 / Peterfalvi (6.6) p-group degree datum** packaged with one
  natural witness: for `χ : IrreducibleCharacter G` of a finite `p`-group, there
  are `d k : ℕ` with `0 < d`, `characterDegree χ = (d : ℂ)`, and `d = p^k`.
  This bridges the existing p-power theorem to S08's natural-degree witnesses and
  prime-power gap data without reopening the representation witness downstream.
- `centralizerInSubgroup` and `VanishesOnTrivialSubgroupCentralizers` encode the
  target shape of (1.2) without adding a new proof stub.
- The shared `ClassFunction` infrastructure now exposes support/restriction
  helpers needed by the Clifford and induced-character proof cores:
  `support_neg`, `support_sub_subset`, `support_restrict`,
  `support_restrict_subset`, `supportedSubmodule_mono`, and
  `restrict_mem_supportedSubmodule`.
- The Clifford proof-core API now exposes restriction-multiplicity algebra in
  both arguments, scalar multiplication in the ambient character argument, and
  ambient conjugation invariance for normal subgroups via
  `restrictionMultiplicity_conjBy_right`.  `IsRestrictionConstituent.conjBy`
  transports constituents, with conjugate irreducibility now supplied by
  `IsIrreducibleCharacter.conjBy`.  At the irreducible-character level,
  `IrreducibleCharacter.conjBy`, `liesOver_conjBy`, and `liesOver_conjBy_iff`
  make the `G`-orbit action on constituents usable without returning to raw
  class-function equalities.  `IrreducibleCharacter.inertia`,
  `subgroup_le_inertia`, `inertiaQuotient`, and
  `conjBy_eq_conjBy_iff_mul_inv_mem_inertia` expose the stabilizer and
  orbit-representative equality criterion needed for the Clifford transversal
  formulation.  `conjByOrbit`, `conjByOrbitEquivRightCosets`, and
  `conjByOrbitEquivLeftCosets` identify this orbit with the right-coset
  quotient and the standard `G ⧸ I_G(θ)` quotient, fixing the parametrization
  needed for the orbit-sum side of Clifford decomposition.
- `inductionCoefficient` and `IsInductionExpansion` encode the (1.3)
  Fourier/induced-character expansion target; numerical Frobenius reciprocity
  remains routed to `InducedCharacter`.
- The induced-character support API includes `conjugatesIntoSet_mono`,
  `conjugatesIntoSet_subset_conjugatesInto`, `conjugatesIntoSet_empty`, and
  `conjugatesIntoSet_univ`, matching the support-control shape used by Dade
  maps.
- `inductionCoefficient_zero_left/right`, `inductionCoefficient_add_left/right`,
  `inductionCoefficient_smul_left`, and `inductionCoefficient_trivial_right`
  expose the elementary coefficient algebra needed by the (1.3) expansion.
- `characterKernel` and `SubsetCharacterKernel` encode the set-level kernel
  containment shape needed for (1.6).
- Kernel basics are now available without unfolding:
  `characterKernel_trivialClassFunction`, `characterKernel_conj`,
  `subsetCharacterKernel_trivialClassFunction`,
  `subsetCharacterKernel_conj_iff`, and `SubsetCharacterKernel.mono`.
- (2026-05-31) **(1.6.a) forward direction landed** (the (6.6) G2.2 use case):
  `subsetCharacterKernel_induce_of_subgroupOf` — for `A ⊴ G` with `A ≤ H`, if
  `(A.subgroupOf H : Set ↥H) ⊆ characterKernel θ` then
  `(A : Set G) ⊆ characterKernel (induce H θ)`.  Built on the RT value formula
  `ClassFunction.induce_apply_of_mem_normal_of_const` (`InducedCharacter.lean`):
  normality makes every conjugate `x⁻¹ a x` of `a ∈ A` land back in `A ≤ H`, so when
  `θ` is constant `= c` on `A` the whole induction sum at `a` collapses to `|G|·c·|H|⁻¹`.
  The (6.6) consumer uses the contrapositive `Z ⊄ Ker (Ind θ) ⟹ Z ⊄ Ker θ`.  The
  **converse** ((1.6.a) `⟸`) is [Is] *Character Theory* Lemma 2.21 (an eigenvalue
  argument on the genuine character `θ`) and is **not yet formalised** — the repo's
  value-based `characterKernel` lacks the representation-kernel eigenvalue machinery.
  Companion constituent infra in `Clifford.lean`:
  `IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver` (`⟨Ind θ, χ⟩ ≠ 0 ↔ LiesOver`,
  Frobenius reciprocity packaging) and `IrreducibleCharacter.exists_liesOver`
  (every `χ ∈ Irr G` lies over some `θ ∈ Irr H`, via completeness on the nonzero `Res χ`).
- (2026-05-31, G2.2 assembly) **(6.6) `X`-characterization, the two honest bricks** assembled
  from the R17 infra above (commit b45164f) and landed in `S03_PreliminaryCharacter.lean`
  (sorry/axiom-free; `#print axioms` = `{propext, Classical.choice, Quot.sound}`; AxiomsCheck
  registered):
  - `not_subsetCharacterKernel_of_not_induce` — the literal **contrapositive** of (1.6.a)-forward,
    `Z ⊄ Ker (Ind_H^G θ) ⟹ Z ⊄ Ker θ`, in the consumer-facing shape (6.6) reads `Z ⊄ Ker θ` from.
  - `exists_inner_induce_ne_zero` — the **constituent-existence half**: every `χ ∈ Irr G` is a
    constituent of `Ind_H^G θ` for some `θ ∈ Irr H` (`⟨Ind_H^G θ, χ⟩ ≠ 0`), by composing
    `exists_liesOver` with `inner_induce_ne_zero_iff_liesOver`.  Unconditional, no center `Z` — the
    existence backbone of the (1.7)-type characterization.
  - **Residual beyond R17** (the one piece (6.6) needs that this round does *not* close): the link
    `Z ⊄ Ker χ ⟹ Z ⊄ Ker (Ind_H^G θ)` for a constituent `χ` — equivalently "an irreducible
    constituent inherits a kernel containment of the ambient character" (`Z ⊆ Ker (Ind θ) ⟹
    Z ⊆ Ker χ`).  This is the general character-value bound `|χ(a)| ≤ χ(1)` with its equality case;
    the repo currently has only the **central**-element Schur equality `‖χ(z)‖² = χ(1)²`
    (`SchurCenterBound.lean:108`), so the general-`a` bound is `needs-infra`.
- (2026-05-31, **DIAGONALIZATION KEYSTONE landed** — closes the G2.2 `needs-infra` above and the
  G2.5 inflation-surjectivity gate; the shared gate of Round-18) The keystone and its character-value
  consequences are now sorry/axiom-free (`#print axioms` = `{propext, Classical.choice, Quot.sound}`,
  AxiomsCheck registered):
  - `OddOrder.RepresentationTheory.rep_eq_id_of_character_eq_one` (`ClassSumAlgebra.lean`): for a
    finite-dim complex rep `ρ` of a finite group and `g`, `ρ.character g = ρ.character 1`
    (`= finrank ℂ V`) ⟹ `ρ g = LinearMap.id`.  `ρ g` finite-order ⇒ semisimple (squarefree
    `X ^ n − 1`); trace = `charpoly.roots.sum` = sum of unit-modulus eigenvalues = degree = count
    forces every eigenvalue `= 1` (triangle equality case
    `all_eq_one_of_norm_eq_one_of_sum_eq_card`, a real-part / non-negative-sum argument); semisimple
    + only eigenvalue `1` ⇒ `eigenspace 1 = ⊤` ⇒ `ρ g − 1 = 0`.  Reuses the
    `character_isIntegral` eigenvalue/trace machinery.
  - `norm_character_le_finrank` + `character_eq_one_iff_rep_eq_id` (`ClassSumAlgebra.lean`): the
    **general** `‖χ(g)‖ ≤ χ(1)` bound (the `needs-infra` piece above, now closed) and its equality
    case both directions — the general-`a` generalization of the central Schur equality.
  - `S03.norm_irreducibleCharacter_le_natDegree` + `S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq`
    (`S03_PreliminaryCharacter.lean`): the **G2.2 constituent-inherits-kernel** equality case in
    consumer form — for irreducible χᵢ with non-negative multiplicities mᵢ, `(∑ mᵢ χᵢ)(g) = (∑ mᵢ
    χᵢ)(1)` ⟹ every `χᵢ` (`mᵢ ≠ 0`) has `g ∈ characterKernel χᵢ`.  A future G2.2 assembly supplies
    the `ψ = ∑ mᵢ χᵢ` decomposition of `Ind_K^L θ` (genuine-character = ℕ-combination of irreducibles
    over `Irr`, still `needs-infra`).
  - **G2.5**: `RepresentationTheory.exists_inflate_eq_of_subset_characterKernel`
    (`InflationCharacter.lean`): every irreducible `χ` of `G` with `N ⊆ ker χ` arises as
    `inflate N χbar`.  The keystone makes `ρ` trivial on `N`, so `ρ` descends through
    `Representation.ofQuotient` to an irreducible `σ` on `G ⧸ N` (`σ` irreducible via the new reverse
    lemma `isIrreducible_of_isIrreducible_comp_of_surjective`) with `χ_σ ∘ mk' = χ`.  With
    `inflate_injective` this is the full degree-preserving bijection `Irr(G ⧸ N) ≃ {χ ∈ Irr G | N ⊆
    ker χ}`, giving the (6.6) degree-sum `Σ_{N ⊆ ker χ} χ(1)² = |G ⧸ N|`.
- (2026-05-31, **keystone PASS 2** — G2.5 degree-sum + G2.2 subrep form landed end-to-end;
  sorry/axiom-free, `#print axioms` = `{propext, Classical.choice, Quot.sound}`, AxiomsCheck
  registered, full `lake build OddOrder`/`OddOrder.AxiomsCheck` green 3360/3343 jobs):
  - **G2.5 degree-sum, now a single theorem** `RepresentationTheory.sumInflatedDegreeSq`
    (`InflationCharacter.lean`, commit 131c124): `∑_{χ ∈ Irr G, N ⊆ ker χ} χ(1)² = |G ⧸ N|` in `ℂ`.
    The keystone-unlocked inflation **bijection** (inject `inflate_injective` + surject
    `exists_inflate_eq_of_subset_characterKernel` + degree `inflate_apply_one` + kernel-subset
    `subset_characterKernel_inflate`) transports Burnside `sumIrreducibleDegreeSq` on `G ⧸ N`
    (`∑_{Irr (G ⧸ N)} χbar(1)² = |G ⧸ N|`) across via `Finset.sum_bij'` (forward `inflate N`,
    inverse = the surjectivity witness `.choose`, left-inverse via `inflate_injective`).  This is
    the literal "(6.6) degree-sum" — previously all four bijection bricks were present but the
    identity itself was not a statement.
  - **G2.2 representation-level constituent-inherits-kernel**
    `RepresentationTheory.subrepresentation_character_eq_one_of_character_eq_one`
    (`ClassSumAlgebra.lean`, next to the keystone): `ρ.character g = ρ.character 1` ⟹ for **every**
    subrepresentation `ρ'` of `ρ`, `ρ'.toRepresentation.character g = ρ'.toRepresentation.character 1`.
    The honest, fully-general (any-universe), no-decomposition-needed form of "a constituent inherits
    a kernel containment of the ambient character" — exactly the structural link (6.6) reads off
    (`Z ⊆ ker (Ind θ) ⟹ Z ⊆ ker χ`).  Proof: keystone `rep_eq_id_of_character_eq_one` gives
    `ρ g = id`, which *restricts* to `id` on the invariant submodule `ρ'.toSubmodule`
    (`LinearMap.restrict` of `id` is `id`), so `χ_{ρ'}(g) = trace id = finrank = χ_{ρ'}(1)`.  This
    complements the already-landed character-value-bound consumer
    `irreducibleCharacter_mem_characterKernel_of_natSum_value_eq` (the `ψ = ∑ mᵢ χᵢ` ℕ-combination
    form).  Note: a `repCharacterClassFunction`/`characterKernel`-phrased wrapper is **not** added —
    `repCharacterClassFunction` restricts `V` to `Type 0` while `ρ'.toSubmodule` is general-universe,
    so the wrapper would be artificial; the `Representation.character` form is the natural altitude.
  - **Residual unchanged**: the one genuine G2.2 `needs-infra` remains the
    **genuine-character decomposition** `Ind_K^L θ = ∑ mᵢ χᵢ` as an ℕ-combination of `Irr L`
    (Maschke multiplicity tracking / completeness with non-negativity — `restrictionMultiplicity_*`
    in `Clifford.lean` give the non-negative *restriction* multiplicities, but the ambient
    `⟨Ind θ, χⱼ⟩ ∈ ℕ` + the `= ∑ ⟨⟩ χⱼ` expansion is not yet assembled).  Both consumer forms above
    discharge the *equality-case* content; only the decomposition that feeds them is outstanding.
- `SecondOrthogonality` now exposes the next matrix proof-core bridge:
  `conjugacyClassSize_pos`,
  `characterTableClassSizeSquareMatrix_mul_columnGram_eq_cardDiagonal`,
  `conjugacyClassSize_mul_characterTableColumnGram_apply`,
  `characterTableConjTranspose_mul_squareMatrix_apply_eq_star_squareColumnPairing`,
  `characterTableSquareColumnPairing_diag_of_weightedRowOrthogonality`, and
  `characterTableSquareColumnPairing_eq_zero_of_ne_of_weightedRowOrthogonality`.
  These close the square/invertible matrix algebra step from weighted row
  orthogonality to square-indexed column diagonal/off-diagonal relations.
- The same conditional relations are now transported back to class-indexed and
  element-representative pairings via
  `characterTableClassColumnPairingOfIndexing_diag_of_weightedRowOrthogonality`,
  `characterTableClassColumnPairingOfIndexing_eq_zero_of_ne_of_weightedRowOrthogonality`,
  `characterTableColumnPairing_diag_of_weightedRowOrthogonality`,
  `characterTableColumnPairing_conj_of_weightedRowOrthogonality`, and
  `characterTableColumnPairing_not_conj_of_weightedRowOrthogonality`; these are
  bundled by `column_orthogonality_cases_of_weightedRowOrthogonality` in the
  same pair-of-cases shape as the final theorem.
- `conjClassesSigmaCarrierEquiv`, `classFunction_innerSum_eq_sum_conjClasses`,
  `characterTableWeightedRowPairing_eq_innerSum`, and
  `CharacterTableWeightedRowOrthogonality.ofRowOrthogonality` now connect
  ordinary row orthogonality to the class-weighted row orthogonality input used
  by the matrix proof core.  `column_orthogonality_cases_ofRowOrthogonality`
  bundles the conditional primitive cases with ordinary row orthogonality input.
  The remaining `column_orthogonality_cases` stub is now the input-supply layer:
  providing canonical finite/indexing and row orthogonality data under the
  public theorem's assumptions.

### (1.4) Tau Isometry — Core Dade Preparation

**主張**: H finite, X ⊆ Irr(H), |X| = n ≥ 2, all χ_i(1) equal. τ: Z[X,H^#] → Z[Irr G, G^#] isometry ⇒ ∃ distinct μ_i ∈ Irr(G), ε = ±1: (χ_i - χ_1)^τ = ε(μ_i - μ_1) for all i.

**証明概要** (induction on n):
- **n=2**: ||(χ_2 - χ_1)^τ||² = 2 ⇒ (χ_2 - χ_1)^τ = e_2 - e_1 (orthonormal decomposition)
- **n=3**: (χ_2 - χ_1)^τ と (χ_3 - χ_1)^τ は 2 つの直交 norm-1 成分の和. 内積 = 1 ⇒ 共通成分 -e_1 共有
- **n > 3, induction**: 各 χ_k (k > 3) について ((χ_k - χ_1)^τ, (χ_i - χ_1)^τ) = 1 for i < k. 2 ケースのみ: (χ_k - χ_1)^τ = e_k - e_1 or e_2 + e_3. 後者は (e_2 + e_3)(1) = 0 = (e_2 - e_3)(1), so e_2(1) = 0 が矛盾.

**mathlib 状況**: **完全新規**. Peterfalvi 独自の補題で「isometry が orthonormal basis を保存する構造」を抽出. 基本 character orthogonality + 有限次元線形代数は mathlib にあり.

**Lean status**: `SignedIrreducibleDifferenceFamily` now names the target
`ε • (μ_i - μ_0)` family.  The row-orthogonality API exposes the key numerical
inputs for the combinatorial core on both sides: nonzero source/target
differences have norm `2`, and two distinct nonzero source/target differences
have inner product `1`.
`irreducibleCharacterDifference` and `isometryDifferenceImage` now name
`χ_i - χ_0` and its `τ` image, and
`isometryDifferenceImage_inner_self_of_ne_zero` /
`isometryDifferenceImage_inner_of_ne_zero_of_ne` transfer the source-side
norm/inner values across `h_isom` without unfolding the raw class-function
differences.  `irreducibleCharacterDifference_apply_one_of_same_degree`,
`IsometryDifferenceImagesVanishAtOne`, and
`SignedIrreducibleDifferenceFamily.signedDifference_apply_one_eq_zero_iff`
record the degree-zero side of (1.4); the abstract structure theorem now
expects the image-side condition `τ(χ_i-χ_0)(1)=0`, matching the reduced
target lattice used in Peterfalvi's proof.
`IsometryDifferencePairNumerics` packages the finite combinatorial inputs for
the next proof-core layer: the zero row, degree-zero condition, norm `2` for
nonzero differences, and mutual inner product `1` for distinct nonzero
differences.  Constructors from `isometryDifferenceImage` and from
`SignedIrreducibleDifferenceFamily.signedDifference` keep the character-theory
orthogonality layer separate from the remaining finite induction.

**形式化**: ~60-80 行 (非自明だが self-contained).

**重要性**: **(1.4) は §4 Dade isometry の主定理 (2.6) への "isometry 構造 lemma"**. これにより、「TI-subset 上の virtual character 等距 → 既約成分への分解保存」が言える.

**2026-05-28 進捗**: (1.4) の証明は bottom-up の 4 層に分解 (詳細は [`issues/0025`](../../issues/0025-peterfalvi-isometry-difference-core.md) の HANDOFF):
**層 1a** `χ(g⁻¹)=conj χ(g)` ✅ 完了 (`RepresentationTheory/CharacterConjugate.lean`, `character_inv`, sorry-free, mathlib ギャップを行列 S-ユニタリ・トリックで充足) → **層 1b** orthonormality discharge (`CharacterTableRowOrthogonality` を定理化、次の着手点) → 層 2 ZIrr Fourier API → 層 3 combinatorial core。

## Isaacs [Is] 1976 → mathlib 対応 (Phase 1 完成想定)

Peterfalvi §3 が明示引用する [Is] results:

| [Is] | Isaacs 内容 | mathlib (Phase 1) | Peterfalvi 利用 |
|------|-------------|-------------------|------------------|
| **Thm 6.32** | # real irreducibles = # self-inverse conj classes | Phase 1 Ch.6 | (1.1) core, (1.2) base |
| **Thm 6.5** | Clifford: Res_H^T ψ when T = I_G(θ) | Phase 1 Ch.6 | (1.5), (1.7) |
| **Lem 2.21** | Kernel under induction | Phase 1 Ch.2 | (1.6) |
| **Thm 6.11** | Induced from stabilizer | Phase 1 Ch.6 | (1.5), (1.7) |
| **Cor 6.28** | Multiplicity-one criterion (abelian normalizer) | Phase 1 Ch.6 | (1.5.b), (1.7.c) |
| **Cor 2.30** | Schur's bound χ(1)² ≤ \|G:Z(χ)\| | Phase 1 Ch.2 — **✅ 実装済** `OddOrder/GroupTheory/RepresentationTheory/SchurCenterBound.lean` (`finrank_sq_le_index` rep 形 + `IsIrreducibleCharacter.exists_degree_sq_le_index` char 形) | (1.8); §8 (6.6)-(6.8); §9 Feit–Sibley |
| **Lem 7.7** | TI-subset Ind isometry | Phase 1 Ch.7 | **§8 (Coherence) L150** (audit 訂正; (1.4) ではない) |
| **Lem 3.2, Cor 3.5** | Cyclotomic arithmetic | Phase 1 Ch.3 | (1.10) |

**観察**: §3 は **新規群論機構を導入しない** — Isaacs Ch.1-7 の **再述 + odd-order specialization**. Phase 2b は §3 を **薄い wrapper layer** として扱える, ただし (1.3)-(1.4) は新規実装.

## mathlib `RepresentationTheory.Character` API

§3 形式化のための既存 API:

```lean
-- Mathlib/RepresentationTheory/Character.lean
def Character (G : Type*) [MonoidHomClass F M G] : Type* := ...
theorem char_orthonormal ... : ⟨V.character, W.character⟩ = if V ≅ W then 1 else 0

-- Mathlib/RepresentationTheory/Induced.lean
def Induced (R : Type*) [Semiring R] (H : Subgroup G) : ... 
theorem frobenius_reciprocity : (Induced_char θ, χ) = (θ, Res χ) := ...
```

**§3 形式化のための gap**:
1. **Character space CF(H,A)** with support A — 新型 wrapper 要
2. **Frobenius reciprocity at character level** — adjunction at Representation level あり, character 翻訳要
3. **Clifford decomposition explicit theorem** — Thm 6.5 形式化要; pieces は Induced API に
4. **Tau isometry (1.4)** — 完全新規

## §3 → §4 (Dade) の依存

§4 Theorem (2.6) (Dade Main Isometry) は以下を前提:
- (1.4) **Tau isometry 構造** — isometry が orthonormal form を保つ ⇒ 差分の符号付き対応
- (1.3) **Fourier decomposition** — 誘導指標を supported basis で展開
- (1.5) **Clifford theory** — 誘導指標の multiplicity + inertia 構造

⇒ **§3 → §4 の strict dependency**: §4 着手前に (1.3), (1.4) 必須.

## Phase 2b §3 形式化着手順

### Stage 1 (Infrastructure, ~100 行)
- `CharacterSupport : Set H → (G → ℂ) → Prop`
- `ClassFunction.restrict : (H → ℂ) → (A → ℂ)`
- Frobenius reciprocity at character level (`Representation.dualPairing` wrapper)

### Stage 2 ((1.1) Odd Order Characterization, ~30 行)
- Phase 1 Thm 6.32 import
- Z/2Z action + oddness で (1.1) 証明

### Stage 3 ((1.5) Clifford Theory, ~60 行)
- Phase 1 Thm 6.5 + Thm 6.11 + Cor 6.28 を Peterfalvi 記法に翻訳
- (1.5.a)-(1.5.e) bundled lemma

### Stage 4 ((1.4) Tau Isometry, ~80 行) ← **§3 の山場**
- `Isometry τ : Z[X,H^#] →ₗ Z[Irr G, G^#]` 定義
- (1.4) induction + orthonormal basis extraction

### Stage 5 ((1.3) Fourier Expansion, ~50 行)
- (1.4) machinery で (1.3.a)-(1.3.b) 証明
- supported orthogonal projection

### Stage 6 ((1.2), (1.6)-(1.8), ~70 行)
- (1.2) Vanishing on trivial centralizers
- (1.6) Kernel descent
- (1.7) Inertia specialization
- (1.8) Height bound

### Stage 7 ((1.9)-(1.10) Cyclotomic, ~50 行)
- (1.9) Galois restriction
- (1.10) Z[ζ_p] modular arithmetic

**合計**: ~350-400 行 Lean 4 for §3 本体. **⚠️ audit 訂正 (2026-05-23)**: Wave 1a infra (`ClassFunction.lean`, `InducedCharacter.lean`, `Clifford.lean`, `Inertia.lean`, `BrauerPermutation.lean`, `IsReal.lean`, `SchurCenterBound.lean`, `IsometryDifferencePair.lean`, `SecondOrthogonality.lean` 合計 ~600 LOC) を含めると **§3 ~1000-1200 LOC**.

## CLAUDE.md `feedback_no_mathlib_wrapper` 整合

- **純粋リネーム禁止**: Peterfalvi 結果は **既存 API の組み合わせ** ((1.5) = Thm 6.5 + 6.11) または **全く新規** ((1.4) tau isometry) のいずれか
- **Character space**: 新型 `CharacterSubspace` は Peterfalvi 専用モジュールに置く (mathlib に PR する候補ではない、特化型)
- **Phase 1 / Phase 2 境界**: Isaacs [Is] Thm 6.2, 6.5, 6.11 等は Phase 1 で独立形式化, §3 で再導出しない. §3 は import + 適用のみ.

## 進捗

- **2026-05-30**: (1.1) 共役差の非退化形 `conjugateDifference_ne_zero_of_ne_trivial_of_odd_card` を追加 (`S03_PreliminaryCharacter.lean`). `|G|` 奇数 + χ 非自明 ⇒ `χ - χ̄ ≠ 0`. 無条件版 `RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'` と既存 `conjugateDifference_ne_zero_iff_not_isReal` の合成. §7 の `χ - χ̄` 構成が非ゼロであることの土台 (§9 (7.9) 経路で消費). AxiomsCheck 登録済 (allowlist clean).
- **2026-05-30**: (1.1) 集合形 `hasNoRealCharacters_nontrivialIrreducibleClassFunctions` を追加 (`S03_PreliminaryCharacter.lean`). 補助定義 `nontrivialIrreducibleClassFunctions G` (= `Irr(G) ∖ {1}` の CF への像) + `mem_…` simp + 単項注入補題 `irreducibleCharacter_mem_…` と併せ, `|G|` 奇数 ⇒ この集合が `HasNoRealCharacters` を満たすことを `not_isReal_of_ne_trivial_of_odd_card'` から導出. §7 coherence の `Hypothesis.no_real_characters` フィールド (= Hypothesis (5.2)(a)) を実際の odd-order 設定で奇数性のみから供給する discharge 補題. AxiomsCheck 登録済 (allowlist clean, sorryAx なし).
- **2026-05-30**: (1.5) Clifford **module 層 BLOCKER A** を `Clifford.lean` に sorry-free 着地 (issue 0026 update (3))。`isSimpleModule_map_conjBySimpleSemilinear`: `H ⊴ G` で `ρ g` が `Res^G_H ρ` の simple `ℂ[H]`-部分加群を simple `ℂ[H]`-部分加群に送る (ρ 既約性不要)。normality `ρ(h)(ρ g v)=ρ g(ρ(g⁻¹hg)v)` を共役 twist `conjBySimpleRingHom g : ℂ[H]→+*ℂ[H]` に関する `ρ g` の **semilinearity** (`conjBySimpleSemilinear`) として実装し, `isSimpleModule_iff_isAtom` + `Submodule.orderIsoMapComapOfBijective` + `OrderIso.isAtom_iff` で atom 性を transport。補助に `restrictRep` (reducible abbrev), `mem_map_conjBySimpleSemilinear` (像 = `ρ g '' N`)。`asModule` の defeq 摩擦は `backward.isDefEq.respectTransparency false` で解消。残 module 層は BLOCKER B (orbit transitivity, 既約性使用) のみ。AxiomsCheck 登録済 (allowlist clean)。
- **2026-05-30**: (1.5) Clifford **gap #5 非負半分**を `Clifford.lean` に sorry-free 着地 (issue 0026 update (4))。`restrictionMultiplicity_nonneg`: 既約指標 `χ`(G), `θ`(H) で `0 ≤ ⟨Res^G_H χ, θ⟩`。**planner sketch の BLOCKER B + Maschke isotype 分解は不要**だった: mathlib `Representation.card_inv_mul_sum_char_mul_char_eq_finrank` が `⟨Res^G_H χ, θ⟩ = dim_ℂ Hom_{ℂ[H]}(σ, ρ|_H)` (= finrank `IntertwiningMap`) を与え, 次元は cast 自然数ゆえ ≥ 0。主補題 `restrictionMultiplicity_eq_finrank_intertwiningMap` (値の公式; gap #1 multiplicity-as-inner-product の核でもある) は `character_inv` で `star(θ h)=σ.char h⁻¹` に直し上記 mathlib 公式へ帰着 (骨格は G-side `characterTableRowOrthogonality` と同型, ただし `char_orthonormal` の 0/1 でなく finrank)。`Representation` レベルゆえ FDRep universe 制約なし・既約性不要。これで gap #5 完全解決 (整数 + 非負)。残 module 層は BLOCKER B のみ (orbit-sum decomposition / single-orbit hypothesis 除去; 非負性は B に非依存と判明)。AxiomsCheck 登録済 (allowlist clean)。

## 未解決 / TODO

1. **Frobenius reciprocity character-level**: 現状 Representation level のみ. character 統一 API 設計要.
2. **Supported character space CF(H,A) 型**: subtype (`{f : H → ℂ // supported_on f A}`) vs predicate? mathlib 慣例 (`Submodule k V`) 準拠.
3. **(1.4) Isometry 形式化戦略**: `LinearIsometry` API or 自前 predicate? TBD.
4. **Phase 1 Isaacs Ch.6 完成日程**: §3 は Phase 1 Ch.6 完成必須. ~2-3 ヶ月先と推定.
5. **Peterfalvi §4 並行設計**: §3 進行中に §4 (Dade) の structure 設計 (`Dade.Isometry` def vs structure) を並行検討要.

---

**作成**: 2026-05-22. **出典**: Peterfalvi `references/peterfalvi/04.3_pp_5_9_*.mmd` (140 行), Phase 1 Isaacs ノート, `notes/peterfalvi/_overview.md`, `notes/meta/phase2_cross_refs.md`.

**次ステップ**: Phase 1 Ch.6 完成モニタ, Phase 2b §3 着手前に Stage 1 (infrastructure) の API 設計 review, §4 設計と並行調整.
