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

## 🛑 重複発覚 → HUB 裁定案件 (2026-07-02, policy 8 適用)

**lane a が S11 で同じ typeP_Galois (9.7) Singer 機構を concurrent 構築していた** (claim-before-build の
search が見落とし — lane a のは Peterfalvi/S11 *所有 file* 内 subgroup-level ゆえ shared-infra scan に掛からず)。
これは policy 8 (重複発覚→hub 裁定) + hub 齟齬 (issue 4014 再配分が lane a の in-progress を勘案せず) の実例。

**重複 map**:
| math | lane a S11 (既存 commit) | 私の σ-theory leaf | 判定 |
|---|---|---|---|
| Galois Singer \|Ū\|∣p^q−1 | `isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm` (`e2a673bd`) | `card_dvd..._irreducible_fpf` | **重複** (両 SingerField wrap、subgroup vs module level) |
| FPF→coprime(\|Ū\|,p−1) | `5efa6b5c` | 同 (SingerField cite) | **重複** |
| refined \|Ū\|∣(p^q−1)/(p−1) | S11:4333 (`Nat.dvd_div_iff_mul_dvd`) | `card_dvd_cyclotomicQuotient...` + 算術核 | **重複** (Galois 側) |
| non-Galois \|Ū\|≤(p−1)^{q−1} | Clifford/Hpart 解析 (S11:4471+、別アプローチ) | imprimitive embedding + `card_le_pow_of_block_scalars` (psi core) | **非重複** (別 route) |
| 汎用算術 (`dvd_div_of_coprime_of_dvd_sub_one` 等) | inline | named 版 | 弱重複 (cite 可) |

**hub に defer する判断** (policy 8 step 3): σ-theory の home 一本化 — (i) lane a の subgroup-level を私の
generic module-level leaf に cite 化するか、(ii) 私の Galois leaf を撤退し lane a の subgroup 版に一本化するか、
(iii) 私は非重複な non-Galois imprimitive engine + psi core + 汎用算術のみ残すか。

**凍結** (policy 8 step 4): 重複 Galois piece (`SingerLineBound.lean` の module-level refined bound) は hub 裁定まで
**これ以上広げない**。非重複部 (non-Galois imprimitive engine `SemilinearImprimitiveBound.lean` の psi core +
embedding、`TypePGaloisUBound` dichotomy) は genuine ゆえ保持。lane d は hub 裁定待ちの間、別 on-spine 上流へ。

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
- [~] step 2 (non-Galois): imprimitivity 分解 + `u ≤ (p−1)^{q−1}`。
      - [x] **generic 算術 engine** (`SemilinearImprimitiveBound.lean`, sorry-free):
        `card_le_pow_of_injective_to_pi` (embedding → `|U|≤|M|^n`) +
        `card_le_pow_sub_one_of_injective_imprimitive` (injective `Ū↪Fin(q−1)→A`, `|A|=a`, `a≤p−1`
        → `u≤(p−1)^{q−1}`)。Coq `psi` embedding (`PFsection9.v:442`) の算術核。
      - [x] **cyclotomic-quotient bridge**: `pow_sub_one_le_cyclotomicQuotient`
        ((p−1)^{q−1}≤(p^q−1)/(p−1)) + `card_le_cyclotomicQuotient_of_injective_imprimitive`
        (imprimitive embedding → u≤(p^q−1)/(p−1))。**両分岐が同一結論に到達** (Galois=SingerLineBound、
        non-Galois=SemilinearImprimitiveBound)。
        ⚠ dup 記録: `pow_sub_one_le_cyclotomicQuotient` = S15 `caseB_u_bound_arith` と同内容。
        infra(GroupTheory)が正位置ゆえ後で S15 を本 leaf cite 化可 (S15=lane d dormant、後日)。
      - [x] **psi embedding injectivity core** (`card_le_pow_of_block_scalars`, sorry-free):
        block scalars `φ : Fin(n+1)→(Ū→*A)` + no-global-scalar (`hconst`) → ratio 埋め込み
        `x↦(φ_{i+1}(x)/φ_0(x))` injective → `|Ū|≤|A|^n=a^{q−1}`。Coq `psi` (PFsection9.v:442) の
        crux を generic 構成。lane a は block scalars φ を供給するだけ (module 分解から)。
      - [ ] **残: 構造的 block 分解** (deep, type-P-specific): Maschke 半単純 (instance 済) +
        W₁-permutation で `Hbar=⊕H1^w` (|H1|=p, q blocks) → 各 block の scalar hom φ_i を取り出す
        + `a∣p−1` (block action → Z_pˣ = SingerField |M|=p 特殊化直接 cite) + `hconst` (Ū に
        nonidentity global scalar 無し = 型 P quotient 構造)。W₁/Ū 依存ゆえ lane a assembly。
- [x] step 3: dichotomy 組立 — **DONE** (`TypePGaloisUBound.lean`,
      `card_le_cyclotomicQuotient_of_faithful_fpf`、sorry-free)。IsSimpleModule で case-split:
      Galois 分岐は完全証明 (SingerLineBound)、non-Galois 分岐は `hReducible` hypothesis
      (caller が imprimitive engine で discharge)。

## 📣 lane a 向け cite signature (hub 裁定「typeP_Galois を再実装せず本 leaf を cite」)

`OddOrder.RepresentationTheory` namespace、`import
OddOrder.GroupTheory.RepresentationTheory.TypePGaloisUBound` で全て入る:

- **u_bound entry point**: `card_le_cyclotomicQuotient_of_faithful_fpf` —
  faithful fpf abelian U on M≅F_p^q → `|U| ≤ (p^q−1)/(p−1)`。Galois 分岐は内部証明済、
  非 Galois 分岐 `hReducible` は下記 engine で discharge。
- **Galois 分岐** (直接も使える): `card_le_cyclotomicQuotient_of_faithful_irreducible_fpf`
  (`|U|∣(p^q−1)/(p−1)`) / `card_le_cyclotomicQuotient_of_faithful_irreducible_fpf` の ≤ 形。
- **非 Galois engine**: `card_le_cyclotomicQuotient_of_injective_imprimitive` —
  imprimitive ratio embedding `Ū↪Fin(q−1)→A` (|A|=a, a≤p−1) → `|U|≤(p^q−1)/(p−1)`。
  lane a は構造的 imprimitivity (Hbar=⊕H1^w、psi injectivity、a∣p−1=SingerField|M|=p) を
  組んで本 engine に渡す (W₁ 依存部)。
- **block a∣p−1**: `RepresentationTheory.SingerField.isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`
  を |M|=p で直接 (別 lemma 不要)。

**残 (lane a assembly、W₁ 依存)**: 構造的 imprimitivity 分解 + psi injectivity。generic 算術・
embedding・両分岐 bound は本 leaf で供給済。

## 参照

- Coq `coq/theories/PFsection9.v:323-560` (`typeP_Galois` / `typeP_Galois_Pn` (9.7.a) / `typeP_Galois_P` (9.7.b))
- issue 4014 (hub 裁定節) / `notes/meta/ft_lane_reallocation_2026_06_28.md` (lane d 再々配分行)
- 既存: `SingerField.lean` / `CyclotomicGaloisAction.lean` / `Clifford*.lean` / `NearFields.lean`
- 下流 consumer: `S15_SAndT_Setup.{basic_structure.u_bound, c_eq_one}` / lane a §11 (Pf 9.7 instance)
