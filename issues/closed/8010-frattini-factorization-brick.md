---
id: 8010
slug: frattini-factorization-brick
title: "§14-independent Frattini factorization lemma for Cor 15.3 hfratt"
created: 2026-06-15
---

# §14-independent Frattini factorization lemma for Cor 15.3 hfratt

## 背景

`S15.mf_hall_centralizer_control_of_inputs` (Cor 15.3 engine, `1d32a3cd`) は (b) fusion control
を組み立てる際、`H ⋬ M` 枝で **Frattini factorization** `M = N_M(H)·Q` を仮説 `hfratt` として
取る。この factorization 自体は §14-非依存の標準群論(BG Cor 15.3 証明の "by the Frattini
argument", mmd L4213)で、いずれ wrapper 配線時に discharge する必要がある。

`notes/bg/s15_16_audit.md` section 13.3 参照。

## やること

- [ ] §14-非依存補題を landing(配置先 = S15_MF.lean、G 所有):
  ```
  theorem frattini_factorization [Finite G] {M Q H : Subgroup G}
      (hQM : Q ≤ M) (hHM : H ≤ M) (hQnorm : (Q.subgroupOf M).Normal)
      (hQHnorm : ((Q ⊔ H).subgroupOf M).Normal) (hdisj : Disjoint Q H)
      (hcop : Nat.Coprime (Nat.card ↥Q) (Nat.card ↥H)) (hsolv : IsSolvable ↥M) :
      ∀ m ∈ M, ∃ n a : G, n ∈ Subgroup.normalizer (H : Set G) ∧ a ∈ Q ∧ m = n * a
  ```
- [ ] 証明: `IsComplement'.exists_conj_of_coprime`(SZ 補群共役, `OddOrder/Mathlib/SchurZassenhausConj.lean:1200`、repo 既存)を `↥(Q ⊔ H)` 内で適用。H と `conj m⁻¹ • H` は `Q` の補群 ⟹ Q-共役 `q` を得て `n := m·q`, `a := q⁻¹`(`m = n·a`、`n ∈ N_G(H)`)。`exists_conj_le_of_isComplement'_of_coprime`(Isaacs Ch03 Main:1223)の subgroupOf juggling がテンプレート。

## 完了条件

`frattini_factorization` が sorry-free + axiom-clean で landing(`#print axioms` = `[propext, Classical.choice, Quot.sound]`)。full build green。

## 参照

- engine: `S15.mf_hall_centralizer_control_of_inputs` (`1d32a3cd`)
- SZ 補群共役: `Subgroup.IsComplement'.exists_conj_of_coprime`
- mmd Cor 15.3 証明 = `references/bg/local-analysis.mmd` L4213
- **優先度低**: Cor 15.3 wrapper の真の binding constraint は `hconj`(Thm 14.4 conjugacy、§16 RData に deferred)ゆえ、この brick 単独では wrapper は完成しない。§16 RData / Thm 14.4 conjugacy 接近時に building。
