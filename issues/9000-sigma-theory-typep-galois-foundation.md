---
id: 9000
slug: sigma-theory-typep-galois-foundation
title: "σ-theory 土台: typeP_Galois (Pf 9.7) の generic semilinear/near-field dichotomy"
created: 2026-07-01
---

# σ-theory 土台: typeP_Galois (Pf 9.7) の generic semilinear/near-field dichotomy

> **CLAIM (lane d, hub 裁定 issue 4014/`ft_lane_reallocation` 2026-07-01)**: generic σ-theory
> (semilinear/near-field) = `typeP_Galois` の土台を新 shared-infra leaf `OddOrder/GroupTheory/**`
> で実証明する。lane a §11 は typeP_Galois を再実装せず本 leaf を **cite**。他レーンは着手前に本 issue を scan。

## 目標

Coq `typeP_Galois := acts_irreducibly U Hbar 'Q` (PFsection9.v:323 = **Pf (9.7)**) の二分岐を
generic に供給する。`U` = abelian complement (repo: `S_U_commutative`)、`Hbar` = Frobenius-kernel
quotient (elementary abelian `p`-group、`F_p`-space、`q`-dim over the U-stabilized field)。

- **Galois** (`typeP_Galois_P`, 9.7.b): U 既約 ⟹ `Hbar ≅ F_{p^q}` 体、`Ubar ↪ F^×`、
  **`u ∣ (p^q−1)/(p−1)`** (U は line を固定しない ⟹ norm でなく projective に効く精緻化)。
- **non-Galois** (`typeP_Galois_Pn`, 9.7.a): U 非既約 ⟹ minimal submodule `H1` (`|H1|=p`)、
  `Hbar = \dprod_{w∈W1bar} H1^w` (q blocks を W1bar が cyclic に置換)、
  `a := |U : C_U(H1)|` が `a>1`・`a ∣ p−1`・`U/C_U(H1)` cyclic・`Ubar ↪ Z_a^{q−1}`
  ⟹ **`u ≤ (p−1)^{q−1}`**。

両分岐から下流 `basic_structure.u_bound` = `u ≤ (p^q−1)/(p−1)` が従う (`caseB_u_bound_arith`
= `(p−1)^{q−1} ≤ (p^q−1)/(p−1)` は既存 sorry-free、non-Galois 側 bridge)。また `c_eq_one` の
Galois 分岐 (Coq `FTtypeP_Ind_Fitting_reg_Fcore` の `typeP_Galois` boolP 分岐、20× cite) の
structural 入力。

## 既存 infra (dup 回避 — hub mandate scan 済 2026-07-01)

再利用する (再実装しない):
- `OddOrder/GroupTheory/RepresentationTheory/SingerField.lean`:
  - `nonempty_singerFieldData` / `SingerFieldData` (既約 abelian action → 体, `M ≃ F_p[C]/I`)。
  - `isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible` (**U cyclic + `u ∣ p^n−1`** = Galois の粗 bound)。
  - `exists_galoisField_repr` (GaloisField 表現)、`coprime_card_sub_one_of_faithful_irreducible_comm_fpf`。
  - cyclotomic 算術 `cyclotomicQuotient_not_dvd_pow_sub_one` / `pow_sub_one_dvd_of_dvd` 等。
- `RepresentationTheory/CyclotomicGaloisAction.lean` (`GaloisCharacter`)、`SkolemNoether.lean`、
  `CliffordMultiplicityOne.lean` / `CliffordSingleOrbit.lean` (Clifford imprimitivity)、
  `ExtraspecialSinger.lean`。
- `Peterfalvi/Appendices/NearFields.lean` (`NearField` 構造・`rightMulAction`・
  `exists_aInvariant_complement_of_elementaryAbelian`・`nearField_field_structure`) — Suzuki 2-rank 用だが
  near-field 構造の再利用可否を精査。

## gap (本 issue で実証明する generic 補題)

1. **Galois line 精緻化**: `isCyclic_and_card_dvd_card_sub_one_*` の `u ∣ p^q−1` を
   **`u ∣ (p^q−1)/(p−1)`** に絞る (U が F^× の scalar `F_p^×` と交わらず projective に効く =
   `U ∩ ⟨center⟩ = 1` / no-fixed-line)。SingerField の field 同型 + `F_p^× ≤ F^×` の index。
2. **non-Galois imprimitivity 分解**: 既約でない faithful abelian U-action on `F_p`-space `V`
   (dim = q, q prime, W1bar が q blocks を cyclic transitive 置換) ⟹ minimal block `H1` (dim 1)
   + `V = ⊕_{i<q} H1^{w_i}` + `a := |U:C_U(H1)| ∣ p−1` + `u ≤ a^{q−1} ≤ (p−1)^{q−1}`。
   Clifford (`CliffordSingleOrbit`) + block-permutation の算術。
3. **dichotomy 組立**: `acts_irreducibly U V` の decidable 分岐で 1/2 を束ねた generic
   `typeP_Galois_dichotomy` (lane a が Pf (9.7) instance で cite)。

## 完了条件

`OddOrder/GroupTheory/RepresentationTheory/` (or 新 sub-leaf) に上記 generic 補題群が sorry-free、
`lake build` 緑。lane a が Pf (9.7) `typeP_Galois_P/Pn` を本 leaf cite で薄く assemble できる signature。

## 進め方 (上流順)

- [x] step 0: 既存 SingerField/Clifford/NearField の被覆域を精読し gap 1-3 の正確な signature 確定。
      → Galois/abelian 側は SingerField が大きく被覆 (`isCyclic_and_card_dvd_card_sub_one` +
      `coprime_card_sub_one_..._fpf`)。gap = line 精緻化 + non-Galois imprimitivity + dichotomy。
- [x] step 1 (Galois): line 精緻化 `u ∣ (p^q−1)/(p−1)` — **DONE** (`SingerLineBound.lean`,
      `card_dvd_cyclotomicQuotient_of_faithful_irreducible_fpf` + 算術核
      `dvd_div_of_coprime_of_dvd_sub_one`、sorry-free、既存 SingerField 2定理 assembly)。
- [ ] step 2 (non-Galois): imprimitivity 分解 + `u ≤ (p−1)^{q−1}`。
- [ ] step 3: dichotomy 組立 + lane a cite signature 告知。

## 参照

- Coq `coq/theories/PFsection9.v:323-560` (`typeP_Galois` / `typeP_Galois_Pn` (9.7.a) / `typeP_Galois_P` (9.7.b))
- issue 4014 (hub 裁定節) / `notes/meta/ft_lane_reallocation_2026_06_28.md` (lane d 再々配分行)
- 既存: `SingerField.lean` / `CyclotomicGaloisAction.lean` / `Clifford*.lean` / `NearFields.lean`
- 下流 consumer: `S15_SAndT_Setup.{basic_structure.u_bound, c_eq_one}` / lane a §11 (Pf 9.7 instance)
