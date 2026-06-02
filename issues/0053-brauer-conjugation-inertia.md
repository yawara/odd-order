---
id: 53
slug: brauer-conjugation-inertia
title: "general Brauer for conjugation → inertia(θ)=H (free W₁-action ⟹ induced irreducibility)"
created: 2026-06-01
---

# general Brauer for conjugation → inertia(θ)=H (free W₁-action ⟹ induced irreducibility)

## 背景

`issues/0046` (Peterfalvi (6.8) Sibley coherence) の **T6 律速** として確定した独立 infra
(handoff 2026-06-01 + `notes/peterfalvi/s08_6_8_assembly_plan.md` §D)。

(6.8) の `Y = S(H')` family は `η_j = Ind_H^L θ` (θ ∈ Irr(H/H')∖{1}, degree 1) で、各 η_j 既約には
[Is]Thm 6.34 `isIrreducibleCharacter_induce_of_inertia_eq` (landed) が要求する **`inertia(θ:CF)=H`**
(= W₁ = L/H が Irr(H)∖{1} に自由作用) が必要。これが §9–§16 の Frobenius-induced irreducibility 全体の鍵。

repo `brauer_permutation_lemma'` (BrauerPermutationUnconditional:196) は **inversion 専用**
(`#RealIrr = #RealClass`)。一般版 `brauer_permutation_lemma` (BrauerPermutation.lean:264) は σ は任意
だが **class 側が `ConjClasses.inv` に固定**。conjugation 版にするには class 側も任意 permutation を
取れる真に一般な Brauer permutation lemma が要る。群レベルの自由作用は Frobenius
(`IsFrobeniusAction.stabilizer_eq_bot` / `fixedPointFree_toMulAut`) で既存 → **Irr レベルへの bridge** が残。

### 数学的核 (Brauer permutation lemma, conjugation form)
α ∈ Aut(H) (典型: H⊴L, g∈L での共役 `conjByMulEquiv g`) に対し
`#{θ∈Irr(H) | conjBy g θ = θ} = #{C∈ConjClasses(H) | g·C·g⁻¹ = C}` (両辺 trace 論法で等しい)。
このとき:
- `conjBy g θ = compHom (conjByMulEquiv g : ↥H →* ↥H) θ` ⟹ `compHom_of_surjective` で既約性保存。
- 互換性 `characterTableEntry (conjBy g θ) C = characterTableEntry θ (g·C·g⁻¹)` は
  `(conjBy g θ)(rep C)=θ(g·rep C·g⁻¹)=θ(rep(g·C·g⁻¹))` (class function)。
- **自由作用** `C_L(h) ≤ H (∀ h∈H∖{1})` ⟹ `g∉H` は ConjClasses(H) で {1} のみ固定
  (`g·⟦h⟧·g⁻¹=⟦h⟧ (h≠1)` ⟺ `∃h'∈H, h'g∈C_L(h)` ⟺ `g∈H·C_L(h)=H`) ⟹ `#fix=1`
  ⟹ Irr 側も `#fix=1` ⟹ 自明指標のみ固定 ⟹ θ≠1 で `g∉inertia θ` ⟹ `inertia θ ≤ H` (逆は常に成立)。

## やること (層構造、各 green commit)

- [x] **Layer A — general Brauer matrix core** (`BrauerPermutation.lean`):
  - `classPerm idx (π : Equiv.Perm (ConjClasses G))` (π の rowColumnEquiv pullback; `classInvPerm` の一般化)
  - `fixedPointsClassPermEquiv` : `{ψ // classPerm idx π ψ = ψ} ≃ {C // π C = C}` (`realClassEquivFixedPointsClassInv` 一般化)
  - 行列代数 core 抽出 (trace 論法): hentry `A(σχ)ψ=A χ(τψ)` ⟹ `(fixedPoints σ).ncard=(fixedPoints τ).ncard`
  - **`brauer_permutation_lemma_general`** (idx,hrow,σ,π,h_compat ⟹ `Nat.card(fixedPoints σ)=Nat.card(fixedPoints π)`)
  - **`brauer_permutation_lemma_general'`** ([Finite] のみ; idx/hrow を `instCharacterTableIndexingOfFinite`+row-orthogonality で放電)
  - `brauer_permutation_lemma` を core 共有に refactor (anti-dup; statement 不変ゆえ downstream 無影響)
- [x] **Layer B — conjugation action を compatible (σ,π) で実体化** (新 file `ConjugationBrauer.lean`, 2026-06-02):
  - `IrreducibleCharacter.conjByPerm g : Equiv.Perm (IrreducibleCharacter ↥H)`
  - `ConjClasses.conjByPerm g : Equiv.Perm (ConjClasses ↥H)` (⟦h⟧↦⟦g·h·g⁻¹⟧, `ConjClasses.map` で定義)
  - `characterTableEntry_conjByPerm` + `brauer_permutation_lemma_general'` による
    `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`。
- [x] **Layer C — free action ⟹ inertia=H** (2026-06-02):
  - `ConjClasses.conjByPerm_one` で単位類固定を formalize。
  - `ConjClasses.fixed_eq_one_of_not_mem_of_centralizer_le` と
    `card_fixedPoints_conjClassPerm_eq_one_of_not_mem_of_centralizer_le` で、
    `g∉H` + `∀ h : H, h ≠ 1 → C_G(h) ≤ H` から固定 conjugacy class が単位類のみ (`#fix=1`) を証明。
  - `not_mem_inertia_of_ne_trivial_of_not_mem_of_centralizer_le` と
    `inertia_eq_of_freeAction` で、非自明 `θ : Irr H` について
    `ClassFunction.inertia (θ : ClassFunction H ℂ) = H` に束ねた。
- [x] **Layer D1 — Frobenius case wiring** (2026-06-02): `IsFrobeniusGroup.centralizer_kernel_le` を
  `inertia_eq_of_freeAction` に渡す `inertia_eq_of_frobeniusGroup` と、6.34 まで合成した
  `isIrreducibleCharacter_induce_of_frobeniusGroup` を `InducedIrreducible.lean` に landing。
  これで (6.8.c1) Frobenius case の `θ≠1 ⟹ Ind_H^L θ ∈ Irr L` prerequisite は直接呼べる。
- [x] **Layer D2a — T6 degree wiring** (2026-06-02):
  SibleyDadeHypothesis.induce_apply_one_eq_card_W1_of_degree_one を S08 に landing。
  degree-one source θ について (Ind_H^L θ)(1)=|W₁| を直接呼べる。
- [ ] **Layer D2b — T6 family wiring**: Y=S(Hprime) の family construction、差分 support、
  および case c2 側の inertia discharge を coherentEqualDegree_fromDade に接続する。

## 完了条件

- Layer A/B/C が sorry/axiom 無 (`#assert_only_allowed_axioms` 3 axiom 全 allowlist)、`lake build OddOrder`/`OddOrder.AxiomsCheck` 緑。
  - 2026-06-02: Layer B 追加後 `lake build OddOrder` 緑。
- ✅ 2026-06-02: `inertia_eq_of_freeAction` (centralizer-free-action 仮説 + θ≠1 ⟹ inertia θ = H) を statement 化・証明。
- ✅ 2026-06-02: Frobenius-group case を `inertia_eq_of_frobeniusGroup` /
  `isIrreducibleCharacter_induce_of_frobeniusGroup` として 6.34 まで packaging。
- ✅ 2026-06-02: S08 で degree-one source θ の (Ind_H^L θ)(1)=|W₁| を packaging。
- 残: Y=S(Hprime) family construction、差分 support、case c2 側の inertia discharge を T6 本体で接続する。

## 参照

- parent: `issues/0046-peterfalvi-s08-6-8-coherence.md` (HANDOFF 2026-06-01 末尾) + `notes/peterfalvi/s08_6_8_assembly_plan.md` §A/§D
- `OddOrder/GroupTheory/RepresentationTheory/BrauerPermutation.lean:264` (general σ, class=inv 固定)
- `OddOrder/GroupTheory/RepresentationTheory/BrauerPermutationUnconditional.lean:196` (`brauer_permutation_lemma'`)
- `OddOrder/GroupTheory/RepresentationTheory/Inertia.lean` (conjBy/conjByMulEquiv/inertia)
- `OddOrder/GroupTheory/RepresentationTheory/InflationCharacter.lean:162` (`compHom_of_surjective`)
- `OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean` ([Is]Thm 6.34 = consumer)
- `OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusActionTI.lean` (group-level free action)
- mmd: `references/peterfalvi/04.8_pp_30_37_*.mmd` L150- ((6.8))
