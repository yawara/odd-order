/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main

/-!
# Isaacs Problems 1F (pp. 40–41) — Brodkey 周辺

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 1F の形式化
(campaign issue 1055)。§1F は Brodkey の定理 (Thm 1.37) とその一般化 (Thm 1.38,
「交わり極小な Sylow 対 `S, T` に対し `O_p(G)` は `D = S ∩ T` の中で `S` でも `T` でも
正規な最大の部分群」) を扱う節で, 演習もその周辺。

* **1F.1**: `M ⊴ G`, `N ⊴ G`, `M ∩ N = 1` なら `M` と `N` は互いに中心化する。
  → **mathlib `Subgroup.commute_of_normal_of_disjoint` がそのままこの主張**
  (証明も Hint どおり交換子 `[m, n] = m⁻¹n⁻¹mn` が `M ∩ N` に入ることを見る)。
  ラッパー方針によりここでは対応を記録するだけで再述しない。
* **1F.2**: `O_p(G) = 1` なら `Z(S) ∩ Z(T) = 1` となる `S, T ∈ Syl_p(G)` が存在する。
  → `exists_sylow_pair_inf_center_eq_bot` (本ファイル)。
* **1F.3**: `G = NP` (`N ⊴ G`, `P ∈ Syl_p(G)`, `N ∩ P = 1`) で `P` の `N` への共役作用が
  忠実なら, `P` は少なくとも 1 つの軌道に忠実に作用する。
  → `exists_faithful_orbit_of_faithful_conj` (本ファイル)。

これで **§1F は 1F.1–1F.3 全問完済**。

## Main results

- `exists_sylow_pair_inf_center_eq_bot` — **Problem 1F.2**。
- `exists_faithful_orbit_of_faithful_conj` — **Problem 1F.3**。
-/

namespace OddOrder.Isaacs.Ch01

open Subgroup

section /- 1F: Problem 1F.2 (p. 41) -/

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- **Isaacs Problem 1F.2** (p. 41)。`O_p(G) = 1` なら, 中心の交わりが自明な
Sylow `p`-部分群の対 `S, T` が存在する。

ここで `Z(S)` は `G` の部分群として `S ⊓ C_G(S)` の形で表す。

交わりの位数が最小 (したがって包含極小) な対 `S, T` を取り
`K := Z(S) ⊓ Z(T)` とおくと `K ≤ S ⊓ T` であり, `K` の元は `S` の全元とも `T` の全元とも
可換なので `S`, `T ≤ N_G(K)`。**Thm 1.38**
(`opCore_eq_inf_of_minimal_sylow_inter`) より `K ≤ O_p(G) = 1`。 -/
theorem exists_sylow_pair_inf_center_eq_bot (h : opCore p G = ⊥) :
    ∃ S T : Sylow p G,
      ((S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G)) ⊓
        ((T : Subgroup G) ⊓ centralizer ((T : Subgroup G) : Set G)) = ⊥ := by
  classical
  have := Fintype.ofFinite (Sylow p G)
  obtain ⟨ST, -, hminST⟩ :=
    (Finset.univ : Finset (Sylow p G × Sylow p G)).exists_min_image
      (fun ST => Nat.card ((ST.1 : Subgroup G) ⊓ (ST.2 : Subgroup G) : Subgroup G))
      ⟨(default : Sylow p G × Sylow p G), Finset.mem_univ _⟩
  obtain ⟨S, T⟩ := ST
  refine ⟨S, T, ?_⟩
  -- 位数最小の対は特に包含極小 (Thm 1.38 が要求する形)
  have hmin : ∀ S' T' : Sylow p G,
      (S' : Subgroup G) ⊓ (T' : Subgroup G) ≤ (S : Subgroup G) ⊓ (T : Subgroup G) →
      (S' : Subgroup G) ⊓ (T' : Subgroup G) = (S : Subgroup G) ⊓ (T : Subgroup G) :=
    fun S' T' hle =>
      Subgroup.eq_of_le_of_card_ge hle (hminST (S', T') (Finset.mem_univ _))
  set K : Subgroup G :=
    ((S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G)) ⊓
      ((T : Subgroup G) ⊓ centralizer ((T : Subgroup G) : Set G)) with hKdef
  have hKD : K ≤ (S : Subgroup G) ⊓ (T : Subgroup G) :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  -- `K` の元は `R` (= `S` または `T`) の全元と可換なので `R ≤ N_G(K)`
  have hnorm : ∀ R : Sylow p G, K ≤ centralizer ((R : Subgroup G) : Set G) →
      (R : Subgroup G) ≤ normalizer (K : Set G) := by
    intro R hKC r hr
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have hc : r * k = k * r := Subgroup.mem_centralizer_iff.mp (hKC hk) r hr
      rwa [show r * k * r⁻¹ = k from by rw [hc]; group]
    · intro hk
      have hc : r * (r * k * r⁻¹) = (r * k * r⁻¹) * r :=
        Subgroup.mem_centralizer_iff.mp (hKC hk) r hr
      have hfix : r * k * r⁻¹ = k := by
        have h1 : r⁻¹ * (r * (r * k * r⁻¹)) = r⁻¹ * ((r * k * r⁻¹) * r) := by rw [hc]
        calc r * k * r⁻¹ = r⁻¹ * (r * (r * k * r⁻¹)) := by group
          _ = r⁻¹ * ((r * k * r⁻¹) * r) := h1
          _ = k := by group
      rwa [hfix] at hk
  have hSC : K ≤ centralizer ((S : Subgroup G) : Set G) := inf_le_left.trans inf_le_right
  have hTC : K ≤ centralizer ((T : Subgroup G) : Set G) := inf_le_right.trans inf_le_right
  have hKle := opCore_eq_inf_of_minimal_sylow_inter S T hmin hKD (hnorm S hSC) (hnorm T hTC)
  rw [h] at hKle
  exact le_bot_iff.mp hKle

end -- Problem 1F.2

section /- 1F: Problem 1F.3 (p. 41) -/

open Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] in
/-- 共役は部分群の位数を変えない。 -/
private lemma card_conj_smul (a : G) (S : Subgroup G) :
    Nat.card ↥(MulAut.conj a • S) = Nat.card ↥S :=
  Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective

omit [Finite G] [Fact (Nat.Prime p)] in
/-- `N ⊴ G`, `N ⊓ P = ⊥` のとき, `x ∈ N` について `P ⊓ xPx⁻¹ = C_P(x)`
(1F.3 の Hint「`|P ∩ P^x|` を最小に」を「`x` の `P`-軌道を最大に」と読み替える鍵)。 -/
private lemma inf_conj_eq_centralizer {N : Subgroup G} [hN : N.Normal] (P : Sylow p G)
    (hinf : N ⊓ (P : Subgroup G) = ⊥) {x : G} (hx : x ∈ N) :
    (P : Subgroup G) ⊓ MulAut.conj x • (P : Subgroup G)
      = (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
  ext u
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨huP, hu⟩
    refine ⟨huP, ?_⟩
    obtain ⟨v, hvP, hv⟩ := (Subgroup.mem_smul_pointwise_iff_exists u (MulAut.conj x) _).mp hu
    have hveq : v = x⁻¹ * u * x := by
      have : x * v * x⁻¹ = u := hv
      rw [← this]; group
    have hvuN : v * u⁻¹ ∈ N := by
      have h1 : u * x * u⁻¹ ∈ N := hN.conj_mem _ hx u
      rw [show v * u⁻¹ = x⁻¹ * (u * x * u⁻¹) from by rw [hveq]; group]
      exact N.mul_mem (N.inv_mem hx) h1
    have hvuP : v * u⁻¹ ∈ (P : Subgroup G) :=
      (P : Subgroup G).mul_mem hvP ((P : Subgroup G).inv_mem huP)
    have hvu : v * u⁻¹ = 1 := Subgroup.mem_bot.mp (hinf ▸ Subgroup.mem_inf.mpr ⟨hvuN, hvuP⟩)
    have hvu' : v = u := by
      have := congrArg (fun z => z * u) hvu
      simpa using this
    have hxu : x * u * x⁻¹ = u := by
      have hvx : x * v * x⁻¹ = u := hv
      rwa [hvu'] at hvx
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have hhx : h = x := hh
    rw [hhx]
    calc x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [hxu]
  · rintro ⟨huP, huC⟩
    refine ⟨huP, ?_⟩
    have hcomm : x * u = u * x := Subgroup.mem_centralizer_iff.mp huC x rfl
    refine (Subgroup.mem_smul_pointwise_iff_exists u (MulAut.conj x) _).mpr ⟨u, huP, ?_⟩
    change x * u * x⁻¹ = u
    rw [hcomm]; group

/-- **Isaacs Problem 1F.3** (p. 41)。`G = NP` (`N ⊴ G`, `P ∈ Syl_p(G)`, `N ⊓ P = 1`) で
`P` の `N` への共役作用が忠実なら, `P` は少なくとも 1 つの `P`-軌道に忠実に作用する。

書籍の Hint どおり `|P ∩ P^x|` が最小になる `x ∈ N` を取る。

* `P ∩ xPx⁻¹ = C_P(x)` (`inf_conj_eq_centralizer`) なので, これは `x` の `P`-軌道が
  最大ということ。
* `x` の軌道 `O` を中心化する `P` の元全体 `K := P ⊓ C_G(O)` は `P` で正規であり,
  さらに `K ≤ C_P(x)` の元は `x` と可換なので `xPx⁻¹` でも正規。
* `G` の Sylow `p`-部分群は全て `nPn⁻¹` (`n ∈ N`) の形なので, `x` の最小性は全 Sylow 対に
  わたる最小性に持ち上がる。よって **Thm 1.38**
  (`opCore_eq_inf_of_minimal_sylow_inter`) が `K ≤ O_p(G)`。
* `O_p(G) ≤ P` と `O_p(G) ⊓ N = ⊥` から (**1F.1** = `commute_of_normal_of_disjoint`)
  `O_p(G)` は `N` を中心化し, 忠実性より `O_p(G) = 1`。ゆえに `K = 1`。 -/
theorem exists_faithful_orbit_of_faithful_conj {N : Subgroup G} [hN : N.Normal] (P : Sylow p G)
    (hNP : ∀ g : G, ∃ n ∈ N, ∃ u ∈ (P : Subgroup G), g = n * u)
    (hinf : N ⊓ (P : Subgroup G) = ⊥)
    (hfaithful : ∀ u ∈ (P : Subgroup G), (∀ n ∈ N, u * n * u⁻¹ = n) → u = 1) :
    ∃ x ∈ N, ∀ u ∈ (P : Subgroup G),
      (∀ g ∈ (P : Subgroup G), u * (g * x * g⁻¹) * u⁻¹ = g * x * g⁻¹) → u = 1 := by
  classical
  have : Fintype ↥N := Fintype.ofFinite _
  -- `O_p(G) = 1`
  have hOp : opCore p G = ⊥ := by
    refine le_bot_iff.mp fun z hz => ?_
    have hzP : z ∈ (P : Subgroup G) := opCore_le P hz
    refine Subgroup.mem_bot.mpr (hfaithful z hzP fun n hn => ?_)
    have hdis : Disjoint (opCore p G) N := by
      rw [disjoint_iff]
      refine le_bot_iff.mp ?_
      calc opCore p G ⊓ N ≤ (P : Subgroup G) ⊓ N := inf_le_inf_right N (opCore_le P)
        _ = N ⊓ (P : Subgroup G) := inf_comm _ _
        _ = ⊥ := hinf
    have hc := Subgroup.commute_of_normal_of_disjoint _ _ inferInstance hN hdis z n hz hn
    rw [Commute, SemiconjBy] at hc
    calc z * n * z⁻¹ = n * z * z⁻¹ := by rw [hc]
      _ = n := by group
  -- 全 Sylow は `n • P` (`n ∈ N`) の形
  have hall : ∀ S' : Sylow p G, ∃ n ∈ N, S' = n • P := by
    intro S'
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S'
    obtain ⟨n, hn, u, hu, rfl⟩ := hNP g
    refine ⟨n, hn, ?_⟩
    rw [← hg, mul_smul, Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hu)]
  -- `|P ⊓ xPx⁻¹|` を最小化する `x ∈ N`
  obtain ⟨x₀, -, hx₀min⟩ :=
    (Finset.univ : Finset ↥N).exists_min_image
      (fun n => Nat.card ((P : Subgroup G) ⊓
        MulAut.conj (n : G) • (P : Subgroup G) : Subgroup G))
      ⟨⟨1, N.one_mem⟩, Finset.mem_univ _⟩
  refine ⟨(x₀ : G), x₀.2, ?_⟩
  set x : G := (x₀ : G) with hxdef
  -- 全 Sylow 対にわたる最小性
  have hminAll : ∀ S' T' : Sylow p G,
      Nat.card ((P : Subgroup G) ⊓ MulAut.conj x • (P : Subgroup G) : Subgroup G) ≤
      Nat.card ((S' : Subgroup G) ⊓ (T' : Subgroup G) : Subgroup G) := by
    intro S' T'
    obtain ⟨a, ha, rfl⟩ := hall S'
    obtain ⟨b, hb, rfl⟩ := hall T'
    have hcoe : ∀ c : G, ((c • P : Sylow p G) : Subgroup G)
        = MulAut.conj c • (P : Subgroup G) := fun c => rfl
    have hconj : MulAut.conj a • (MulAut.conj (a⁻¹ * b) • (P : Subgroup G))
        = MulAut.conj b • (P : Subgroup G) := by
      rw [smul_smul, ← map_mul, show a * (a⁻¹ * b) = b from by group]
    have hsplit : ((a • P : Sylow p G) : Subgroup G) ⊓ ((b • P : Sylow p G) : Subgroup G)
        = MulAut.conj a • ((P : Subgroup G) ⊓
            MulAut.conj (a⁻¹ * b) • (P : Subgroup G)) := by
      rw [Subgroup.smul_inf, hconj, hcoe, hcoe]
    rw [hsplit, card_conj_smul]
    exact hx₀min ⟨a⁻¹ * b, N.mul_mem (N.inv_mem ha) hb⟩ (Finset.mem_univ _)
  -- 軌道を中心化する `P` の元全体
  intro u huP hufix
  set O : Set G := {y | ∃ g ∈ (P : Subgroup G), y = g * x * g⁻¹} with hOdef
  set K : Subgroup G := (P : Subgroup G) ⊓ centralizer O with hKdef
  have hxO : x ∈ O := ⟨1, one_mem _, by group⟩
  have huK : u ∈ K := by
    refine ⟨huP, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro y ⟨g, hg, rfl⟩
    have h := hufix g hg
    calc g * x * g⁻¹ * u = (u * (g * x * g⁻¹) * u⁻¹) * u := by rw [h]
      _ = u * (g * x * g⁻¹) := by group
  have hKC : K ≤ centralizer ({x} : Set G) := by
    intro k hk
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have hhx : h = x := hh
    rw [hhx]
    exact Subgroup.mem_centralizer_iff.mp hk.2 x hxO
  have hKD : K ≤ (P : Subgroup G) ⊓ MulAut.conj x • (P : Subgroup G) := by
    rw [inf_conj_eq_centralizer P hinf x₀.2]
    exact le_inf inf_le_left hKC
  -- `P` の元による共役は `K` を保つ
  have hstep : ∀ z ∈ (P : Subgroup G), ∀ w ∈ K, z * w * z⁻¹ ∈ K := by
    intro z hz w hw
    refine ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hz hw.1)
      ((P : Subgroup G).inv_mem hz), Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro y ⟨h, hh, rfl⟩
    have hmem : z⁻¹ * (h * x * h⁻¹) * z ∈ O :=
      ⟨z⁻¹ * h, (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hz) hh, by group⟩
    have hcw := Subgroup.mem_centralizer_iff.mp hw.2 _ hmem
    calc h * x * h⁻¹ * (z * w * z⁻¹)
        = z * ((z⁻¹ * (h * x * h⁻¹) * z) * w) * z⁻¹ := by group
      _ = z * (w * (z⁻¹ * (h * x * h⁻¹) * z)) * z⁻¹ := by rw [hcw]
      _ = (z * w * z⁻¹) * (h * x * h⁻¹) := by group
  have hPnorm : (P : Subgroup G) ≤ normalizer (K : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    refine fun k => ⟨fun hk => hstep g hg k hk, fun hk => ?_⟩
    have h2 := hstep g⁻¹ ((P : Subgroup G).inv_mem hg) _ hk
    rwa [show g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k from by group] at h2
  -- `xPx⁻¹` の元による共役も `K` を保つ (`K` の元は `x` と可換)
  have hstepQ : ∀ y ∈ MulAut.conj x • (P : Subgroup G), ∀ w ∈ K, y * w * y⁻¹ ∈ K := by
    intro y hy w hw
    obtain ⟨g, hg, hgy⟩ := (Subgroup.mem_smul_pointwise_iff_exists y (MulAut.conj x) _).mp hy
    have hyx : y = x * g * x⁻¹ := hgy.symm
    have hwx : x⁻¹ * w * x = w := by
      have hc : x * w = w * x := Subgroup.mem_centralizer_iff.mp (hKC hw) x rfl
      calc x⁻¹ * w * x = x⁻¹ * (w * x) := by group
        _ = x⁻¹ * (x * w) := by rw [hc]
        _ = w := by group
    have hgw : g * w * g⁻¹ ∈ K := hstep g hg w hw
    have hgwx : x * (g * w * g⁻¹) * x⁻¹ = g * w * g⁻¹ := by
      have hc : x * (g * w * g⁻¹) = (g * w * g⁻¹) * x :=
        Subgroup.mem_centralizer_iff.mp (hKC hgw) x rfl
      rw [hc]; group
    have : y * w * y⁻¹ = g * w * g⁻¹ := by
      rw [hyx, ← hgwx]
      calc x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹
          = x * (g * (x⁻¹ * w * x) * g⁻¹) * x⁻¹ := by group
        _ = x * (g * w * g⁻¹) * x⁻¹ := by rw [hwx]
    rw [this]
    exact hgw
  have hQnorm : MulAut.conj x • (P : Subgroup G) ≤ normalizer (K : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    refine fun k => ⟨fun hk => hstepQ y hy k hk, fun hk => ?_⟩
    have hyinv : y⁻¹ ∈ MulAut.conj x • (P : Subgroup G) :=
      (MulAut.conj x • (P : Subgroup G)).inv_mem hy
    have h2 := hstepQ y⁻¹ hyinv _ hk
    rwa [show y⁻¹ * (y * k * y⁻¹) * y⁻¹⁻¹ = k from by group] at h2
  -- **Thm 1.38** を `(P, xPx⁻¹)` に当てる
  have hmin : ∀ S' T' : Sylow p G,
      (S' : Subgroup G) ⊓ (T' : Subgroup G) ≤
        (P : Subgroup G) ⊓ ((x • P : Sylow p G) : Subgroup G) →
      (S' : Subgroup G) ⊓ (T' : Subgroup G) =
        (P : Subgroup G) ⊓ ((x • P : Sylow p G) : Subgroup G) :=
    fun S' T' hle => Subgroup.eq_of_le_of_card_ge hle (hminAll S' T')
  have hKle := opCore_eq_inf_of_minimal_sylow_inter P (x • P) hmin hKD hPnorm hQnorm
  rw [hOp] at hKle
  exact Subgroup.mem_bot.mp (hKle huK)

end -- Problem 1F.3

end OddOrder.Isaacs.Ch01
