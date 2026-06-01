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
- [ ] **Layer B — conjugation action を compatible (σ,π) で実体化** (新 file `ConjugationBrauer.lean`):
  - `IsIrreducibleCharacter (conjBy g θ)` (= `compHom (conjByMulEquiv g) θ` 経由) + `conjByPermIrr g : Equiv.Perm (IrreducibleCharacter ↥H)`
  - `conjClassPerm g : Equiv.Perm (ConjClasses ↥H)` (⟦h⟧↦⟦g·h·g⁻¹⟧, `Quotient.lift`, well-defined ← H normal)
  - 互換性補題 + Layer A 適用 ⟹ `Nat.card(fixedPoints(conjByPermIrr g))=Nat.card(fixedPoints(conjClassPerm g))`
- [ ] **Layer C — free action ⟹ inertia=H**:
  - `conjClassPerm g` は単位類固定; `g∉H`+free `C_L(h)≤H` ⟹ 単位類のみ固定 ⟹ `#fix=1`
  - ⟹ `#fix(conjByPermIrr g)=1` ⟹ 自明指標のみ ⟹ `inertia_eq_of_freeAction` (θ≠1 ⟹ `inertia θ = H`)
- [ ] **Layer D — wiring** (T6 proper / 別 commit): free-action を Frobenius (case c1) 等から放電し
  6.34 + `index_H_eq_card_W1` + difference-support engine で `Y` coherent。

## 完了条件

- Layer A/B/C が sorry/axiom 無 (`#assert_only_allowed_axioms` 3 axiom 全 allowlist)、`lake build OddOrder`/`OddOrder.AxiomsCheck` 緑。
- `inertia_eq_of_freeAction` (free-action 仮説 + θ≠1 ⟹ inertia θ = H) が statement 化・証明される。
- これと 6.34 で (6.8) T6 の `Y` family 既約性が機械的に従う (Layer D は別 issue/commit でも可)。

## 参照

- parent: `issues/0046-peterfalvi-s08-6-8-coherence.md` (HANDOFF 2026-06-01 末尾) + `notes/peterfalvi/s08_6_8_assembly_plan.md` §A/§D
- `OddOrder/GroupTheory/RepresentationTheory/BrauerPermutation.lean:264` (general σ, class=inv 固定)
- `OddOrder/GroupTheory/RepresentationTheory/BrauerPermutationUnconditional.lean:196` (`brauer_permutation_lemma'`)
- `OddOrder/GroupTheory/RepresentationTheory/Inertia.lean` (conjBy/conjByMulEquiv/inertia)
- `OddOrder/GroupTheory/RepresentationTheory/InflationCharacter.lean:162` (`compHom_of_surjective`)
- `OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean` ([Is]Thm 6.34 = consumer)
- `OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusActionTI.lean` (group-level free action)
- mmd: `references/peterfalvi/04.8_pp_30_37_*.mmd` L150- ((6.8))
