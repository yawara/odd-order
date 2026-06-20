---
id: 2014
slug: wielandt-91-completion
title: "lane-h drives Pf (9.1) Wielandt fixed-point formula to completion"
created: 2026-06-21
---

# lane-h drives Pf (9.1) Wielandt fixed-point formula to completion

## 背景

ユーザー指示 (2026-06-21): lane-h POLE-2 frontier が cross-lane gate で exhausted →
**「§14 体構造 |P|=p^q に着手」** を選択。その honest path を辿ると:

```
Pf (13.2.b) |P|=p^q  (basic_structure.P_order / card_Q_eq, S15_SAndT, sorry)
  ← Pf (10.11) [Type II] + Pf (11.7) [Type III]      (S12 / S13, sorry)
  ← Pf (9.3) |H|=|W₂|^q + Pf (9.6) chief factor       (S11, typeII_III_IV_order_relations, sorry)
  ← Pf (9.1) Wielandt fixed-point formula             (CoprimeAction.wielandt_fixedPoint_frobenius)
```

⟹ **|P|=p^q は Pf (9.1) Wielandt の fixed-point formula に bottom-out**。これがチェーン全体の
deepest pole。`|C_H(UE)|^|E| · |H| = |C_H(E)|^|E| · |C_H(U)|` (Frobenius L=U⋊E が可解 H に coprime
作用)。mathlib 不在 (mathlib の "wielandt" は primitive permutation group のみ)。

## 現状 (2026-06-21 調査)

(9.1) は **lane-f の parked infrastructure** (設計 = `notes/peterfalvi/s11_wielandt_91_design.md`,
2026-06-17〜18)。**~70% 完成**:
- ✅ 全 abstract cores が 0-sorry, axiom-clean: I-1 (modular Brauer orbit-equality, Teichmüller-free,
  `CenterSimplesOrbit`/`CenterOrbitFree`/`FreeActionOrbitCount`), I-2 (isotypic decomp,
  `CenterModuleDecomp`), I-3 + 抽象 free-orbit engine (`WielandtCounting`/`FreeOrbitModuleCount`
  `finrank_eq_card_mul_finrank_invariants_of_free`), step 2 (⋆ `finrank_elab_identity`, modulo (†))。
- ❌ **唯一の残 sorry = `wielandt_fixedPoint_frobenius`** (`CoprimeAction.lean:160`)。3 corollary は
  main formula から証明済 (sorry-free)。残務は **carrier-level wiring** のみ。

## やること (resume⁵ NEXT, 設計 notes 末尾)

- [ ] **(†) module wiring** (lane-f coupled rep-theory 領域): `htag` = `dim[V,U] = |E|·dim([V,U]⊓V^E)`
      を done engine 群 (centerProj isotypic + free-orbit + base change) から discharge。
      items 0-3: (0) E-conjugation → simplesAction module bridge ★ / (1) 3d.3c を real carrier に wire /
      (2) (†) realize / (3) I-4 base change F_p→F̄_p。
- [x] **el-ab card↔dim bridge `|V|=p^dim`** = **既存** `IsElementaryAbelian.card_eq_pow_finrank`
      (`PRank.lean:106`, `Nat.card G = p ^ finrank (ZMod p) (Additive G)`)。再導出不要、直接 cite。
- [x] **fixed-point 対応** = **DONE** (`WielandtElabBridge.lean`, sorry-free, full build 3872 green):
      `elabRepresentation p φ` (el-ab V の ZMod p-表現) + `card_fixedSubgroup_eq_card_invariants`
      (group `C_V(X)=fixedSubgroup φ X` ↔ module `invariants (ρ.comp X.subtype)` の card 一致、
      `Additive.ofMul` で同一集合) + `card_fixedSubgroup_eq_pow_finrank` (`|C_V(X)|=p^dim V^X`)。
- [x] **per-factor (9.1) card 恒等式** = **DONE** (`WielandtElabBridge.lean`, sorry-free, build 3872 green):
      `card_fixedSubgroup_wielandt_of_dim` — (⋆) 次元恒等式 `hdim` を仮定し、bridge で `p^(·)` 化して
      `|C_V(⊤)|^|E|·|V| = |C_V(E)|^|E|·|C_V(U)|`。`hdim` = `finrank_elab_identity` の結論 ((†) modulo)
      ゆえ (†) は依然 isolate。helper `invariants_comp_top_subtype` (`invariants(ρ.comp ⊤)=ρ.invariants`)。
- [x] **I-5 chief-step multiplicativity** (single step) = **DONE** (`CoprimeFixedPoints.lean`,
      sorry-free + axiom-clean, full build 3873 green): `card_fixedSubgroup_eq_mul` —
      `|C_H(X)| = |C_H(X) ⊓ N| · |C_{H/N}(X)|` for `N ◁ H` `L`-invariant, coprime + solvable.
      核 = reduction map `C_H(X) →* H/N` の image = `C_{H/N}(X)` (surjectivity =
      `map_fixedSubgroup_eq_fixedSubgroup_quotient` = Isaacs Cor 3.28
      `OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient`), kernel = `C_H(X) ⊓ N` (Lagrange +
      first iso)。helper `isAInvariant_comp_subtype` (restriction along `X ≤ L`)。
      ⚠ naming wart: 誘導商作用は `OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom`
      (Ch04 Main で `namespace Ch04` 内に Ch03 修飾名で `def` ⟹ Ch04 prefix が付く; dot 不可)。
      clean 化は source の `_root_.` 修飾要 = spine 全 rebuild ゆえ別 issue で coordinate。
- [ ] **chief-series telescoping**: 上記 single-step を `L`-invariant chief series で反復 →
      `|C_H(X)| = ∏_i |C_{V_i}(X)|`。要 = 強帰納 (`Nat.card H`) で minimal `L`-invariant normal `N`
      (el-ab) を取り、`N` に per-factor (⋆) を、`H/N` に IH を適用、X∈{UE,E,U} の single-step ×
      `|H|=|N|·|H/N|` を掛けて (9.1) を組む。新ピース = minimal `L`-invariant normal の存在 (el-ab) +
      `C_H(X)⊓N` ↔ `C_N(X)` の per-factor bridge card 一致。
- [ ] **assembly** → `wielandt_fixedPoint_frobenius` sorry-free 化 (architecture: 最終 assembly は
      `WielandtElabBridge` を要し CoprimeAction の下流ゆえ、statement+carrier の downstream 再配置が要る)。
- [ ] 下流 (別 issue 可): (9.3) `typeII_III_IV_order_relations` → (9.6) → (10.11)/(11.7) → (13.2.b)
      `basic_structure.P_order` / `card_Q_eq` を順に de-gate。

## 完了条件

`wielandt_fixedPoint_frobenius` が sorry-free + axiom-clean。full build green。
(下流の |P|=p^q de-gate は後続 issue。)

## lane 調整

(9.1) ファイル群 (`GroupTheory/CoprimeAction.lean` + `GroupTheory/RepresentationTheory/*`) は設計上
lane-f 所有だが lane-f は §16/§14 に pivot して **parked**。lane-h の現 §14 体構造タスクが (9.1) 完成を
要するため lane-h が pickup。ファイルは lane-f の現 frontier (S14/S15/S16) と disjoint ゆえ merge 衝突
低。設計 notes に lane-h pickup を記録。**(†) module wiring は lane-f の coupled 領域**ゆえ、lane-h は
まず group-theoretic な I-5 chief-series assembly + el-ab bridge を進め、(†) は lane-f 知見と要調整。

## 参照

- 設計: `notes/peterfalvi/s11_wielandt_91_design.md` (lane-f, resume⁵ "NEXT" がロードマップ)
- assembly point: `OddOrder/GroupTheory/CoprimeAction.lean:156` (`wielandt_fixedPoint_frobenius`)
- (⋆): `OddOrder/GroupTheory/RepresentationTheory/WielandtCounting.lean:176` (`finrank_elab_identity`)
- chief series: `OddOrder/GroupTheory/ChiefFactor.lean`; Cor 3.28:
  `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean:808`
- 下流 scaffolding: `S11_MaximalII_III_IV.lean` (9.3/9.4/9.6), `S12_MaximalIII_IV_V.lean` (10.11),
  `S13_MaximalIII_IV.lean` (11.7), `S15_SAndT.lean` (13.2.b)
