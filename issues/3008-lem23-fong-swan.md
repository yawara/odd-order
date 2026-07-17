---
id: 3008
slug: lem23-fong-swan
title: "BG Lem 2.3 (Fong–Swan): dim M | |G| for abs. irred. FG-module, solvable G"
created: 2026-07-18
---

# BG Lem 2.3 (Fong–Swan): dim M | |G| for abs. irred. FG-module, solvable G

## 背景

BG §2 の残ギャップ (survey 正本 = `notes/meta/three_books_full_survey_2026_07_16.md` L303,
L308)。2026-07-18 時点で BG §2 の未形式化は **Lem 2.3** と **Lem 2.7** のみ (Prop 2.1 は
lane c が 2026-07-17 に完成、Prop 2.2(a)(b) は 2026-07-18 に char-free 化)。document 順で
Lem 2.3 が次。

**BG 本文の証明 (mmd L659-668) は elementary** — Brauer lifting でなく Clifford + 帰納:

> |G| 帰納。|G|>1, F 代数閉に帰着。H ◁ G を素数 index p で取る。L を M_H の既約
> 部分加群。帰納で dim L | |H|。x ∈ G-H を取る。
> - **case (i)** L ≅ L^x ⟹ Prop 2.2 で L = M_H ⟹ dim M = dim L | |H| | |G|。
> - **case (ii)** L ≇ L^x ⟹ M_H = L ⊕ Lx ⊕ ... ⊕ Lx^{p-1} (p 個 pairwise 非同型、
>   直和) ⟹ dim M = p·dim L | p|H| = |G|。

Prop 2.2 と Clifford 半単純性を 2026-07-18 に char-free 化したので、この elementary 証明が
任意標数で通る (Fong-Swan の modular 版を経由しない)。

## やること

- [ ] **reduction**: 絶対既約 M over F ⟹ base change で F 代数閉に帰着 (dim・|G| 不変)。
      lane c の `IsAbsolutelyIrreducible` + `baseChangeRepresentation_isIrreducible` が土台。
- [ ] **prime-index normal subgroup**: solvable finite nontrivial G ⟹ ∃ H ◁ G, [G:H] prime。
      既存 `exists_normal_index_prime_of_solvable` (S07_Hypothesis75.lean:50) が **private** —
      de-privatize / 共有 leaf へ抽出 (mathlib に無い)。
- [ ] **case (i)**: `restriction_isSimpleModule` (CliffordMultiplicityOne, char-free) で
      M_H ≅ L。hgen は [G:H]=p prime + x∉H から、hconj は L≅L^x を G=⟨H,x⟩ で全 g へ伝播。
- [ ] **case (ii)** [= 主要ギャップ、issue 9110 の shared infra]: L ≇ L^x ⟹ dim M = p·dim L。
      module-level induced-rep irreducibility over general alg-closed field が必要
      (repo は ℂ character-level のみ; mathlib は Rep.ind に既約性なし)。
      e=1 (multiplicity) の証明ルート案: (A) M ≅ Ind_H^G L (trivial inertia)、または
      (B) End_{kG}(M)=k (Burnside) = End_{kH}(M_H) の ρ(x)-fixed points の次元計算 = e²。
- [ ] **strong induction on |G|** で組み立て、full book strength (general solvable G, general F)。

## 完了条件

`OddOrder.RepresentationTheory` に `dim M ∣ |G|` (絶対既約 FG-module, solvable G) を
sorry-free・axiom-clean で。survey 正本の Lem 2.3 行を「済」に更新。

## 参照

- shared infra: [[9110]] module-level induced-rep Clifford (case ii の brick)
- 依存: `CliffordMultiplicityOne.restriction_isSimpleModule`,
  `CliffordAlgClosed.{isSemisimpleModule_resRep_of_isIrreducible,isIsotypicOfType_of_conjugates,
  iSup_map_conjSemilinearEnd_eq_top}`, `AbsolutelyIrreducible.IsAbsolutelyIrreducible`
- BG mmd L655-668
