# Pf (9.7.a) 非Galois imprimitive u-bound — W2 (issue 9000) instance tail の crux

> lane-a, 2026-07-09。W2 = typeP_Galois instance tail の非Galois branch。**目標** =
> `caseA_u_le_cyclotomicQuotient : chars.u ≤ (chief.p ^ data.q - 1)/(chief.p - 1)` を
> `CliffordCaseAData` から実証明し、`CliffordCaseAData.Ubar_embeds_product := True` (opaque, S11:6710)
> を genuine content に置換する。consumer = S15 `basic_structure.u_bound` (S15:2171 sorry) →
> `c_eq_one` (Pf 13.12, S16 で ~16× cite)。

## 状態 (2026-07-09)

- **✅ landed (commit 23e65432)**: shared bridge `OddOrder/GroupTheory/RepresentationTheory/AInvariantSubrep.lean`
  — `aInvariantSubrep (hJ : IsAInvariant φ J) : Subrepresentation (elabRepresentation p φ)` +
  `card_aInvariantSubrep` (submodule card = subgroup card)。sorry-free。
- **✅ 生成 foundation (sorry-free 済)**: `card_le_cyclotomicQuotient_of_blocks`
  (`TypePGaloisUBound.lean:71`) — `ρ : Representation (ZMod p) U M` + `B : Fin(n+1) → Subrepresentation ρ`
  (各 `Nat.card (B i).toSubmodule = p`) + **hconst** ⟹ `Nat.card U ≤ (p^(n+1)-1)/(p-1)`。内部で
  lineScalarChar/ratio/injectivity を処理。
- **残 = producer 組立 + hconst (Frobenius crux)**。

## 生成 lemma 適用の object 対応 (S11)

| 生成 lemma の引数 | S11 の実体 |
|---|---|
| acting group `U` | `↥(uActionHom data chief).range` = Ū (= `chars.u` = `chars.u_eq_card_quotient`) |
| module `M` | `Additive (↥data.H ⧸ chief.N)` = Additive H̄ |
| `[Module (ZMod p) M]` | `chief.quotient_elementaryAbelian.zmodModule` (letI) |
| `ρ` | `elabRepresentation chief.p (uActionHom data chief).range.subtype` |
| `B i` | `aInvariantSubrep (Hpart i の range-invariance)` |
| `hBcard` | `card_aInvariantSubrep` + `caseA.Hpart_order` (= chief.p) |
| `hcardM = p^q` | `chiefFactor_quotient_card chief` (Additive は card 不変) |
| `hq : 1 ≤ q` | `data.q` prime ≥ 2 |
| 結論 | `Nat.card ↥range ≤ (p^q-1)/(p-1)` を `chars.u_eq_card_quotient` で `chars.u ≤ …` に |

**packaging の小 bridge**:
1. `IsAInvariant (uActionHom) (Hpart i)` → `IsAInvariant (range.subtype) (Hpart i)` (同一 automorphism 集合)。
2. `CommGroup ↥(uActionHom).range` instance — image abelian (`hComm : ∀ a b, Commute (φU a) (φU b)`,
   `chiefFactor_caseB_action_fpf` 節に既存パターン) から `{ inferInstanceAs (Group _) with mul_comm := … }`。

## ★ hconst (genuine §9 crux) = Coq `psi` injectivity (`PFsection9.v:442-484`)

**主張**: `∀ ū : Ū, (∀ i, ū が block i に作用する scalar = block 0 の scalar) → ū = 1`。

**論証** (Coq `suffices Kpsi: 'ker (Morphism psiM) = C` + `Frobenius_trivg_cent frobUW1c`):
1. ū が全 block に共通 scalar λ で作用 ⟹ block は H̄ を span (`Hpart_iSup`) ⟹ ū = λ·(-) (scalar power map)
   as element of MulAut(H̄) = GL(H̄)。
2. scalar power map は MulAut(H̄) で**中心的** (全 automorphism と可換)。
3. ∴ ū は W̄₁-conjugation で不変 (W̄₁ ⊆ MulAut(H̄) と可換) = W̄₁-fixed in Ū。
4. **Frobenius `(U⊔W₁)/C = Ū ⋊ W̄₁`** (Coq `frobUW1c`, Lean は `typeP_uW1_frobenius` S11:176 から
   quotient 導出): W̄₁ は Ū に fpf 作用 ⟹ C_Ū(W̄₁) = 1 ⟹ ū = 1。
   - Coq 実装: `quotient_cents2r` で `[ker(psi), W₁] ⊆ C` (共通 scalar ⟹ [ū,w]∈C)、
     `Frobenius_trivg_cent frobUW1c` で W̄₁-central part = trivial。

**Lean port の要点**: additive scalar (lineScalarChar) ↔ multiplicative MulAut(H̄) の橋渡し +
`typeP_uW1_frobenius` からの quotient-Frobenius fpf 抽出が要 work。`Hpart_orbit`/`caseA_wOrbit`
(W₁-orbit 構造) が W̄₁-action の handle。

## build 戦略

新 leaf `OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean` (S11 import、fast iterate)。
producer を hconst 補題に還元して先に packaging を build-green 化 → hconst を Frobenius で埋める。
完成後 `CliffordCaseAData.Ubar_embeds_product` を本 bound に置換 (or S15 が直接 cite)。

## ✅ packaging landed (2026-07-09, commit 337c9dbe) — 残 = hconst 1 本のみ

`S11_ImprimitiveUBound.lean` build-green (real sorry = 1 = hconst)。sorry-free で landed:
- `isAInvariant_range_subtype` (φ-invariant → range.subtype-invariant)
- `uActionHom_range_comm` (Ū abelian、`typeP_commutator_U_centralizes_H` 経由)
- `caseA_u_le_cyclotomicQuotient` の全 packaging (aInvariantSubrep で block→Subrep、
  `card_le_cyclotomicQuotient_of_blocks` 適用、`chars.u_eq_card_quotient` で |Ū|=u、
  finCongr で Fin q↔Fin((q-1)+1)、instance diamond は H̄/Ū の CommGroup を canonical Group
  明示 base で構成し解消)。

**⟹ bound 全体が唯一の hconst (block engine の 4th 引数、line ~118 inline sorry) に還元。**

## hconst の precise 分解 (次 iteration)

`hconst : ∀ ū : Ū, (∀ i, lineScalarChar (block i) ū = lineScalarChar (block 0) ū) → ū = 1`

1. **共通 scalar → global scalar**: 各 block で `lineScalarChar (block i) ū = λ` (共通) ⟹
   `ū` は各 Hpart i 上で power map `x ↦ x^λ` ⟹ blocks span (`Hpart_iSup=⊤`) ゆえ H̄ 全体で。
   infra: **`mulAut_eq_one_of_eq_id_on_iSup` (S11:2186)** を `ū · (powermap λ)⁻¹` (= id on blocks)
   に適用。加法 `lineScalarChar_smul` ↔ 乗法 power map の橋渡しが要 (Additive.ofMul 経由)。
2. **λ·id は MulAut(H̄)=GL(H̄) で中心的** (scalar は全 automorphism と可換)。
3. **中心的 ū は W̄₁-conjugation 不変** ⟹ `ū ∈ C_Ū(W̄₁)`。
4. **Frobenius fpf**: `C_Ū(W̄₁) = 1`。⚠ **最深部・infra gap**: `typeP_uW1_frobenius` は
   `IsFrobeniusGroup (U⊔W₁) (U.subgroupOf) (W₁.subgroupOf)` を与えるが、**quotient Frobenius
   `(U⊔W₁)/C = Ū⋊W̄₁`** (Coq `frobUW1c` = `Frobenius_quotient frobUW1`) への降下 + その
   `Frobenius_trivg_cent` が Lean に無い → 新 infra 要 (or 直接: 「u∈U, [u,W₁]⊆C ⟹ u∈C」を
   U⊔W₁ Frobenius fpf `fixedPointFree_toMulAut` FrobeniusActionTI:394 から導く)。
   Coq 実装 = `quotient_cents2r` で `[ker(psi),W₁]⊆C` + `Frobenius_trivg_cent frobUW1c`。

step 1-3 は tractable、**step 4 (quotient-Frobenius fpf) が genuine infra 投資**。
