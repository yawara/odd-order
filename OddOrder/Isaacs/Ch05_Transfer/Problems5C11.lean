/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Problems
import OddOrder.Isaacs.Ch05_Transfer.Problems5C10

/-!
# Isaacs Problem 5C.11 — `H ⊆ Z(N_G(H))` なる Hall 部分群 (p. 164)

**主張**: `H` が `G` の Hall 部分群 (`gcd(|H|, |G:H|) = 1`) で `H ⊆ Z(N_G(H))` なら,
`|H|` の任意の素因数 `p` に対し `G` は正規 `p`-補群をもつ。

**証明** (書籍の hint = `|G|` に関する帰納法; ここでは `G` を固定して**部分群の位数**に関する
帰納法に組み替えた — 型レベルの再帰も商群も要らない):

`H ⊆ Z(N_G(H))` から `H` は可換 (`H ≤ N_G(H)` ゆえ)。`p ∣ |H|` なので `H` の Sylow `p`-部分群 `P`
は Hall 性より `G` の Sylow `p`-部分群でもある。Burnside (Thm 5.13) を使うには
**`N_G(P) ≤ C_G(P)`** を出せばよく、これは次の補題 (`le_centralizer_aux`) の `M := N_G(P)` の場合:

> `H ≤ M` かつ `M ≤ N_G(P)` なる任意の部分群 `M` について `M ≤ C_G(P)`。

`|M|` に関する帰納法。`M ≤ N_G(H)` なら仮定 `H ⊆ Z(N_G(H))` からそのまま `M ≤ C_G(H) ≤ C_G(P)`。
そうでないときは `H` が Sylow 部分群たちで生成される (`iSup_sylow_eq_top`) ことから、
**`M` が正規化しない `H` の Sylow `q`-部分群 `Q`** が取れる。Hall 性より `Q` は `G` の Sylow
`q`-部分群でもある。ここで

* `L := M ⊓ N_G(Q)` は `M` の真部分群で `H ≤ L ≤ N_G(P)` ⟹ 帰納法で `L ≤ C_G(P)`,
* `C := M ⊓ C_G(P)` は `M ≤ N_G(P)` ゆえ `M`-共役不変で `Q ≤ H ≤ C`,

なので **Frattini 論法** (`C` 内の Sylow `q`-共役性) が `M = C · L` を与え、両因子が `C_G(P)` に
入るので `M ≤ C_G(P)`。

⭐ 書籍の hint の 2 段 (「`N_G(P) < G` なら `P` は `N_G(P)` の中心」「`P ⊴ G` かつ `N_G(Q) < G`
なら `P` は `N_G(Q)` の中心」) は、この形の帰納法では**同じ 1 本の補題**に融合する。
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise

variable {G : Type*} [Group G]

section /- 5C.11: `H ⊆ Z(N_G(H))` なる Hall 部分群 (p. 164) -/

/-- 有限群はその Sylow 部分群たち (各素因数につき全ての Sylow) で生成される。

位数の各素冪 `q^k ∣ |K|` は Sylow `q`-部分群の位数を割り、その Sylow は右辺の join に入るので
`|K| ∣ |⨆ …|`。Lagrange の逆向きと合わせて位数が一致し `⊤` に等しい。 -/
theorem iSup_sylow_eq_top (K : Type*) [Group K] [Finite K] :
    (⨆ (q : (Nat.card K).primeFactors) (Q : Sylow (q : ℕ) K), (Q : Subgroup K)) = ⊤ := by
  classical
  refine Subgroup.eq_top_of_card_eq _ (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card _) ?_)
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r k hr hrk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp
  have hrp : r.Prime := hr
  haveI : Fact r.Prime := ⟨hrp⟩
  have hrdvd : r ∣ Nat.card K := (dvd_pow_self r hkpos.ne').trans hrk
  have hrmem : r ∈ (Nat.card K).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hrp, hrdvd, Nat.card_pos.ne'⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r K))
  have hQle : (Q : Subgroup K) ≤
      ⨆ (q : (Nat.card K).primeFactors) (Q : Sylow (q : ℕ) K), (Q : Subgroup K) :=
    le_iSup_of_le ⟨r, hrmem⟩ (le_iSup_of_le Q le_rfl)
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le hQle)
  rw [Q.card_eq_multiplicity]
  exact pow_dvd_pow r ((Nat.Prime.pow_dvd_iff_le_factorization hrp Nat.card_pos.ne').mp hrk)

/-- Hall 部分群 `H` の Sylow `q`-部分群 (`q ∣ |H|`) を `G` に押し出すと位数がちょうど
`q` の `|G|` での重複度になる。`|H|` と `|G:H|` が互いに素なので `q ∤ |G:H|`、よって `q` の
`|H|` での重複度と `|G|` での重複度が一致するため。 -/
theorem card_map_subtype_eq_multiplicity [Finite G] {H : Subgroup G}
    (hHall : Nat.Coprime (Nat.card ↥H) H.index) {q : ℕ} [Fact q.Prime]
    (hq : q ∣ Nat.card ↥H) (Q : Sylow q ↥H) :
    Nat.card ↥((Q : Subgroup ↥H).map H.subtype) = q ^ (Nat.card G).factorization q := by
  have hqindex : ¬ q ∣ H.index := by
    intro hd
    have h1 : q ∣ Nat.gcd (Nat.card ↥H) H.index := Nat.dvd_gcd hq hd
    rw [hHall] at h1
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h1)
  have hGcard : Nat.card G = Nat.card ↥H * H.index := (Subgroup.card_mul_index H).symm
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective H), Q.card_eq_multiplicity,
    hGcard, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
  simp [Nat.factorization_eq_zero_of_not_dvd hqindex]

/-- Hall 部分群の Sylow 部分群を `G` に押し出すと `G` の Sylow 部分群になる
(`card_map_subtype_eq_multiplicity` の Sylow 版)。 -/
theorem exists_sylow_coe_eq_map_subtype [Finite G] {H : Subgroup G}
    (hHall : Nat.Coprime (Nat.card ↥H) H.index) {q : ℕ} [Fact q.Prime]
    (hq : q ∣ Nat.card ↥H) (Q : Sylow q ↥H) :
    ∃ S : Sylow q G, (S : Subgroup G) = (Q : Subgroup ↥H).map H.subtype :=
  ⟨Sylow.ofCard _ (card_map_subtype_eq_multiplicity hHall hq Q), rfl⟩

/-- **5C.11 の核** (書籍 hint の 2 段を融合した帰納補題).

`H` は Hall で `H ⊆ Z(N_G(H))`、`P` は `H` に含まれる Sylow `p`-部分群とする。
このとき `H ≤ M` かつ `M ≤ N_G(P)` なる任意の部分群 `M` は `C_G(P)` に含まれる。

`Nat.card ↥M ≤ n` の `n` に関する帰納法 (`M` は `G` の部分群のまま動くので型レベル再帰は不要)。 -/
private theorem le_centralizer_aux [Finite G] {H : Subgroup G}
    (hHall : Nat.Coprime (Nat.card ↥H) H.index)
    (hZ : H ≤ Subgroup.centralizer (Subgroup.normalizer (H : Set G) : Set G))
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hPH : (P : Subgroup G) ≤ H) :
    ∀ n : ℕ, ∀ M : Subgroup G, Nat.card ↥M ≤ n → H ≤ M →
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) →
      M ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
  classical
  -- `H` は可換 (`H ≤ N_G(H)` と `H ⊆ Z(N_G(H))`)
  have hHab : H ≤ Subgroup.centralizer (H : Set G) :=
    hZ.trans (Subgroup.centralizer_le (by exact_mod_cast Subgroup.le_normalizer))
  have hHP : H ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) :=
    hHab.trans (Subgroup.centralizer_le (by exact_mod_cast hPH))
  intro n
  induction n with
  | zero =>
    intro M hMcard _ _
    have := Nat.card_pos (α := ↥M)
    omega
  | succ n ih =>
    intro M hMcard hHM hMP
    by_cases hMN : M ≤ Subgroup.normalizer (H : Set G)
    · -- `M ≤ C_G(H) ≤ C_G(P)`
      refine le_trans (fun m hm => ?_) (Subgroup.centralizer_le (by exact_mod_cast hPH))
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact ((Subgroup.mem_centralizer_iff.mp (hZ hh)) m (hMN hm)).symm
    · -- `M` が正規化しない `H` の Sylow 部分群を取り出す
      obtain ⟨i, hi⟩ :
          ∃ i : (q : (Nat.card ↥H).primeFactors) × Sylow (q : ℕ) ↥H,
            ¬ M ≤ Subgroup.normalizer
              (((i.2 : Subgroup ↥H).map H.subtype : Subgroup G) : Set G) := by
        by_contra hall
        push Not at hall
        refine hMN (le_trans (le_iInf hall) ?_)
        have hsup : (⨆ i : (q : (Nat.card ↥H).primeFactors) × Sylow (q : ℕ) ↥H,
            ((i.2 : Subgroup ↥H).map H.subtype : Subgroup G)) = H := by
          rw [iSup_sigma,
            show (⨆ (q : (Nat.card ↥H).primeFactors) (Q : Sylow (q : ℕ) ↥H),
                ((Q : Subgroup ↥H).map H.subtype : Subgroup G))
                = ((⨆ (q : (Nat.card ↥H).primeFactors) (Q : Sylow (q : ℕ) ↥H),
                    (Q : Subgroup ↥H)).map H.subtype) by simp only [Subgroup.map_iSup],
            iSup_sylow_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        calc ⨅ i : (q : (Nat.card ↥H).primeFactors) × Sylow (q : ℕ) ↥H,
              Subgroup.normalizer (((i.2 : Subgroup ↥H).map H.subtype : Subgroup G) : Set G)
            ≤ Subgroup.normalizer
                ((⨆ i : (q : (Nat.card ↥H).primeFactors) × Sylow (q : ℕ) ↥H,
                  ((i.2 : Subgroup ↥H).map H.subtype : Subgroup G) : Subgroup G) : Set G) :=
              Subgroup.iInf_normalizer_le_normalizer_iSup _
          _ = Subgroup.normalizer (H : Set G) := by rw [hsup]
      obtain ⟨⟨q, hqmem⟩, Q⟩ := i
      haveI : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hqmem⟩
      -- `Qsub` は `G` の Sylow `q`-部分群
      obtain ⟨QS, hQS⟩ := exists_sylow_coe_eq_map_subtype hHall
        (Nat.dvd_of_mem_primeFactors hqmem) Q
      have hQH : (QS : Subgroup G) ≤ H := hQS ▸ Subgroup.map_subtype_le _
      have hQP : (QS : Subgroup G) ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) :=
        hQH.trans hHP
      have hi' : ¬ M ≤ Subgroup.normalizer ((QS : Subgroup G) : Set G) := by
        rw [hQS]; exact hi
      -- `L := M ⊓ N_G(Q)` は `M` の真部分群、帰納法が使える
      have hHL : H ≤ M ⊓ Subgroup.normalizer ((QS : Subgroup G) : Set G) := le_inf hHM
        ((hHab.trans (Subgroup.centralizer_le (by exact_mod_cast hQH))).trans
          (Subgroup.centralizer_le_normalizer _))
      have hLM : M ⊓ Subgroup.normalizer ((QS : Subgroup G) : Set G) ≤ M := inf_le_left
      have hLcard : Nat.card ↥(M ⊓ Subgroup.normalizer ((QS : Subgroup G) : Set G)) <
          Nat.card ↥M := by
        rcases lt_or_eq_of_le (Subgroup.card_le_of_le hLM) with h | h
        · exact h
        · exact absurd (Subgroup.eq_of_le_of_card_ge hLM h.ge) fun heq => hi' (heq ▸ inf_le_right)
      have hLC : M ⊓ Subgroup.normalizer ((QS : Subgroup G) : Set G) ≤
          Subgroup.centralizer ((P : Subgroup G) : Set G) :=
        ih _ (by omega) hHL (hLM.trans hMP)
      -- `C := M ⊓ C_G(P)` は `M`-共役不変
      have hCle : ∀ m ∈ M, MulAut.conj m • (M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G))
          ≤ M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
        intro m hm x hx
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
          show ((MulAut.conj m)⁻¹ • x : G) = m⁻¹ * x * m by
            rw [← map_inv]; simp [MulAut.smul_def]] at hx
        obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hx
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have : m * (m⁻¹ * x * m) * m⁻¹ ∈ M :=
            M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)
          simpa [mul_assoc] using this
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy' : m⁻¹ * y * m ∈ ((P : Subgroup G) : Set G) := by
            have h := (Subgroup.mem_normalizer_iff.mp (hMP hm)) (m⁻¹ * y * m)
            rw [show m * (m⁻¹ * y * m) * m⁻¹ = y by group] at h
            exact h.mpr hy
          have hcomm := Subgroup.mem_centralizer_iff.mp hxC _ hy'
          calc y * x = m * ((m⁻¹ * y * m) * (m⁻¹ * x * m)) * m⁻¹ := by group
            _ = m * ((m⁻¹ * x * m) * (m⁻¹ * y * m)) * m⁻¹ := by rw [hcomm]
            _ = x * y := by group
      -- Frattini 論法: `M = C · L`
      intro m hm
      have hQC : (QS : Subgroup G) ≤ M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) :=
        le_inf (hQH.trans hHM) hQP
      have hQ'C : ((m • QS : Sylow q G) : Subgroup G) ≤
          M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
        rw [Sylow.coe_subgroup_smul]
        exact le_trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQC) (hCle m hm)
      obtain ⟨c, hc⟩ := MulAction.exists_smul_eq
        (↥(M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)))
        (QS.subtype hQC) ((m • QS).subtype hQ'C)
      have hAB : MulAut.conj c •
            ((QS : Subgroup G).subgroupOf
              (M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)))
          = (MulAut.conj m • (QS : Subgroup G)).subgroupOf
              (M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)) := by
        have h := congrArg
          (fun S : Sylow q ↥(M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)) =>
            (S : Subgroup ↥(M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)))) hc
        simpa only [Sylow.coe_subgroup_smul, Sylow.coe_subtype] using h
      have hinf1 : (QS : Subgroup G) ⊓
          (M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)) = (QS : Subgroup G) :=
        inf_eq_left.mpr hQC
      have hinf2 : (MulAut.conj m • (QS : Subgroup G)) ⊓
          (M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G))
          = MulAut.conj m • (QS : Subgroup G) :=
        inf_eq_left.mpr (by rw [← Sylow.coe_subgroup_smul]; exact hQ'C)
      have hkey : ((c : G)) • QS = m • QS := by
        apply Sylow.ext
        rw [Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul]
        have h := congrArg
          (Subgroup.map (M ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)).subtype) hAB
        rwa [Ch01.map_conj_smul, Subgroup.subgroupOf_map_subtype, hinf1,
          Subgroup.subgroupOf_map_subtype, hinf2] at h
      have hmem : m⁻¹ * (c : G) ∈ Subgroup.normalizer ((QS : Subgroup G) : Set G) :=
        Sylow.smul_eq_iff_mem_normalizer.mp (by rw [mul_smul, hkey, inv_smul_smul])
      have hnL : m⁻¹ * (c : G) ∈ M ⊓ Subgroup.normalizer ((QS : Subgroup G) : Set G) :=
        Subgroup.mem_inf.mpr
          ⟨M.mul_mem (M.inv_mem hm) ((Subgroup.mem_inf.mp c.2).1), hmem⟩
      have hmeq : m = (c : G) * (m⁻¹ * (c : G))⁻¹ := by group
      rw [hmeq]
      exact Subgroup.mul_mem _ ((Subgroup.mem_inf.mp c.2).2)
        (Subgroup.inv_mem _ (hLC hnL))

/-- **Isaacs Problem 5C.11** (p. 164) ⭐: `H` が `G` の Hall 部分群 (位数と指数が互いに素) で
`H ⊆ Z(N_G(H))` なら, `|H|` の任意の素因数 `p` に対し `G` は正規 `p`-補群をもつ。

`H ⊆ Z(N_G(H))` は「`H` の元は `N_G(H)` の全ての元と可換」として述べた
(`H ≤ N_G(H)` は常に成り立つのでこれで書籍の主張と同値, とくに `H` は可換)。 -/
theorem hasNormalPComplement_of_hall_le_center_normalizer [Finite G] {H : Subgroup G}
    (hHall : Nat.Coprime (Nat.card ↥H) H.index)
    (hZ : H ≤ Subgroup.centralizer (Subgroup.normalizer (H : Set G) : Set G))
    {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card ↥H) :
    HasNormalPComplement p G := by
  classical
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p ↥H))
  obtain ⟨P, hP⟩ := exists_sylow_coe_eq_map_subtype hHall hp Q
  have hPH : (P : Subgroup G) ≤ H := hP ▸ Subgroup.map_subtype_le _
  have hHab : H ≤ Subgroup.centralizer (H : Set G) :=
    hZ.trans (Subgroup.centralizer_le (by exact_mod_cast Subgroup.le_normalizer))
  have hHP : H ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) :=
    hHab.trans (Subgroup.centralizer_le (by exact_mod_cast hPH))
  refine hasNormalPComplement_of_sylow_normalizer_le_centralizer P ?_
  exact le_centralizer_aux hHall hZ P hPH _ (Subgroup.normalizer ((P : Subgroup G) : Set G))
    le_rfl (hHP.trans (Subgroup.centralizer_le_normalizer _)) le_rfl

end

end OddOrder.Isaacs.Ch05
