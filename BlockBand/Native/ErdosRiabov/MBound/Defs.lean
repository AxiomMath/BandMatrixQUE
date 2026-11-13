module

public import BlockBand.Native.ErdosRiabov.Prop.Bridge
public import BlockBand.Native.ErdosRiabov.Evol.TermListAlg

/-!
# `M`-bounds: bound predicates, patterns, the nonzero extension of `patM`

Definitions and elementary facts for the bounds on the deterministic `M`-chains.

* Bound predicates, for `P : PsiData N`, a length `n`, a number `A`:
  `MBAvB P n A` (`|Tr[M S^{x_n}]| ≤ A ℓη s^av_n` for all `t ∈ [0,1]`, patterns and sites; the
  averaged `M`-term is `Evol.avM`), `MBIsoB P n I` (`|M_{aa}| ≤ I √(ℓη) s^iso_n(a,x',a)`), the
  restrictions `MBAvSat` (no non-saturated factor, `¬ Propagator.HasDesatFactor σ`) and
  `MBAvNs` (`HasDesatFactor σ`), and the induction hypothesis `MBIndHyp P k A I`
  (all lengths `1 ≤ n < k`);
* `mbLambda d N = c_m⁻¹ log((C₀+1)N)`;
* `hasDesatFactor_of_odd`, `propFactorOf_eq_sat_of_not_desat`;
* the nonzero extension `mbPatMExt z σ` of `Psi.patM z σ` (value `m(z)` off `[1,k]`), with
  `‖·‖ < 1`, `≠ 0`, the locality of `Split.chainM` in the spectral data
  (`mb_chainTilde_congr_m`, `mb_chainM_congr`), and `mb_mChain_eq_ext`;
* the multilinearity of `Split.chainTilde` in one observable (`mb_chainTilde_sum_obs`);
* the VS spectral parameters `zParam t (patConj b m)` and `|z_{j,t} - z_{j+1,t}| = 2η_t` for
  conjugate neighbours (`mb_zParam_patConj`, `norm_mb_zParam_sub`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Propagator
open scoped ComplexConjugate BigOperators

variable {N : ℕ}

/-!
## Bound predicates
-/

/-- `AvB(n, A)`: for all `t ∈ [0,1]`, patterns and sites,
`|Tr[M^{(t)}_{[1,n]}(x') S^{x_n}]| ≤ A · ℓ_tη_t · s^av_{n,t}(x)`. -/
def MBAvB (P : PsiData N) (n : ℕ) (A : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ (σ : Fin n → Bool) (x : Fin n → Fin N),
    ‖Evol.avM P σ x t‖ ≤ A * (P.lEta t * P.sAv x t)

/-- `IsoB(n, I)`: `|(M^{(t)}_{[1,n]}(x'))_{aa}| ≤ I √(ℓ_tη_t) s^iso_{n,t}(a,x',a)`. -/
def MBIsoB (P : PsiData N) (n : ℕ) (I : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ (σ : Fin n → Bool) (a : Fin N) (x : Fin n → Fin N),
    ‖P.mChain σ x t a‖ ≤ I * (Real.sqrt (P.lEta t) * P.sIso a a x t)

/-- `AvB` restricted to saturated patterns (no non-saturated factor). -/
def MBAvSat (P : PsiData N) (n : ℕ) (A : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ (σ : Fin n → Bool), ¬ HasDesatFactor σ → ∀ x : Fin n → Fin N,
    ‖Evol.avM P σ x t‖ ≤ A * (P.lEta t * P.sAv x t)

/-- `AvB` restricted to non-saturated patterns. -/
def MBAvNs (P : PsiData N) (n : ℕ) (A : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ (σ : Fin n → Bool), HasDesatFactor σ → ∀ x : Fin n → Fin N,
    ‖Evol.avM P σ x t‖ ≤ A * (P.lEta t * P.sAv x t)

/-- The induction hypothesis `H(k)`: `AvB(n, A n) ∧ IsoB(n, I n)` for all `1 ≤ n < k`. -/
def MBIndHyp (P : PsiData N) (k : ℕ) (A I : ℕ → ℝ) : Prop :=
  ∀ n, 1 ≤ n → n < k → MBAvB P n (A n) ∧ MBIsoB P n (I n)

theorem mbAvB_of_sat_ns {P : PsiData N} {n : ℕ} {A₁ A₂ A : ℝ} (h1 : MBAvSat P n A₁)
    (h2 : MBAvNs P n A₂) (hA₁ : A₁ ≤ A) (hA₂ : A₂ ≤ A) (hpos : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ x : Fin n → Fin N, 0 ≤ P.lEta t * P.sAv x t) : MBAvB P n A := by
  intro t ht σ x
  by_cases hσ : HasDesatFactor σ
  · exact (h2 t ht σ hσ x).trans (mul_le_mul_of_nonneg_right hA₂ (hpos t ht x))
  · exact (h1 t ht σ hσ x).trans (mul_le_mul_of_nonneg_right hA₁ (hpos t ht x))

/-- `Λ = c_m⁻¹ log((C₀+1)N)`, the bound of `∫_0^t η_s⁻¹ ds`. -/
def mbLambda (d : VSData) (N : ℕ) : ℝ := d.cm⁻¹ * Real.log ((d.C0 + 1) * N)

/-!
## Patterns
-/

/-- Every pattern of odd length has a non-saturated factor. -/
theorem hasDesatFactor_of_odd {k : ℕ} (hk : Odd k) (σ : Fin k → Bool) : HasDesatFactor σ := by
  by_contra hno
  have hk0 : 0 < k := hk.pos
  have hflip : ∀ j : Fin k, patNext σ j = !σ j := by
    intro j
    by_contra h
    apply hno
    refine ⟨j, ?_⟩
    cases h1 : σ j <;> cases h2 : patNext σ j <;> simp_all
  have hval : ∀ i (hi : i < k), σ ⟨i, hi⟩ = (σ ⟨0, hk0⟩ ^^ decide (i % 2 = 1)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := hflip ⟨i, by omega⟩
      unfold patNext at h1
      rw [dite_eq_left (show i + 1 < k from hi)] at h1
      rw [h1, ih (by omega)]
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · have : (i + 1) % 2 = 1 := by omega
        simp [h, this]
      · have : (i + 1) % 2 = 0 := by omega
        simp [h, this]
  have hlast := hflip ⟨k - 1, by omega⟩
  unfold patNext at hlast
  rw [dite_eq_right (by simp only []; omega)] at hlast
  have hodd : (k - 1) % 2 = 0 := by
    obtain ⟨r, hr⟩ := hk
    omega
  rw [hval (k - 1) (by omega), hodd] at hlast
  cases h : σ ⟨0, hk0⟩ <;> simp [h] at hlast

/-- A pattern without non-saturated factor has all factors saturated. -/
theorem propFactorOf_eq_sat_of_not_desat {k : ℕ} {σ : Fin k → Bool}
    (hσ : ¬ HasDesatFactor σ) : propFactorOf σ = fun _ => .sat := by
  funext j
  by_contra h
  exact hσ ⟨j, (propFactorOf_ne_sat_iff σ j).mp h⟩

/-!
## The nonzero extension of `patM`
-/

/-- `patM z σ` on `[1,k]`, `m(z)` elsewhere (so that `Split.WardStatement` applies). -/
def mbPatMExt (z : ℂ) {k : ℕ} (σ : Fin k → Bool) (i : ℕ) : ℂ :=
  if 1 ≤ i ∧ i ≤ k then patM z σ i else semicircleM z

theorem mbPatMExt_of_mem (z : ℂ) {k : ℕ} (σ : Fin k → Bool) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ k) : mbPatMExt z σ i = patM z σ i := by
  rw [mbPatMExt, ite_eq_left ⟨h1, h2⟩]

theorem norm_mbPatMExt_lt_one {z : ℂ} (hz : z.im ≠ 0) {k : ℕ} (σ : Fin k → Bool) (i : ℕ) :
    ‖mbPatMExt z σ i‖ < 1 := by
  unfold mbPatMExt
  split_ifs
  · exact norm_patM_lt_one hz σ i
  · exact norm_semicircleM_lt_one hz

theorem semicircleM_ne_zero' (z : ℂ) : semicircleM z ≠ 0 :=
  ne_zero_of_root (semicircleM_dyson z)

theorem mbPatMExt_ne_zero (z : ℂ) {k : ℕ} (σ : Fin k → Bool) (i : ℕ) : mbPatMExt z σ i ≠ 0 := by
  unfold mbPatMExt
  split_ifs with h
  · have h' : 1 ≤ i ∧ i ≤ k := h
    unfold patM
    rw [dite_eq_left h']
    cases σ ⟨i - 1, by omega⟩
    · exact semicircleM_ne_zero' z
    · simpa [VS.patConj] using semicircleM_ne_zero' z
  · exact semicircleM_ne_zero' z

/-- `M̃_{[j,l]}` only reads the spectral data `m_j, …, m_l`. -/
theorem mb_chainTilde_congr_m (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) {m m' : ℕ → ℂ}
    (A : ℕ → Fin N → ℂ) (n : ℕ) :
    ∀ j l, l - j = n → (∀ p, j ≤ p → p ≤ l → m p = m' p) →
      Split.chainTilde σ S m A j l = Split.chainTilde σ S m' A j l := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j l hn hm
  rw [Split.chainTilde_eq σ S m A j l, Split.chainTilde_eq σ S m' A j l]
  by_cases hjl : j < l
  · simp only [hjl, ite_true]
    rw [hm j le_rfl hjl.le, hm l hjl.le le_rfl,
      ih (l - (j + 1)) (by omega) (j + 1) l rfl fun p hp hp' => hm p (by omega) hp']
    congr 2
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Ioo.mp hi
    rw [hm i (by omega) (by omega), ih (i - j) (by omega) j i rfl fun p hp hp' => hm p hp
        (by omega), ih (l - i) (by omega) i l rfl fun p hp hp' => hm p (by omega) hp']
  · simp only [hjl, ite_false]

/-- `M_{[j,l]}` only reads `m_j, …, m_l` and `A_j, …, A_{l-1}`. -/
theorem mb_chainM_congr (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) {m m' : ℕ → ℂ}
    {A A' : ℕ → Fin N → ℂ} {j l : ℕ} (hm : ∀ p, j ≤ p → p ≤ l → m p = m' p)
    (hA : ∀ p, j ≤ p → p < l → A p = A' p) :
    Split.chainM σ S m A j l = Split.chainM σ S m' A' j l := by
  rw [Evol.chainM_congr σ S m hA, Split.chainM, Split.chainM,
    mb_chainTilde_congr_m σ S A' (l - j) j l rfl hm]
  congr 1
  exact Finset.prod_congr rfl fun p hp => by
    have := Finset.mem_Icc.mp hp
    exact hm p this.1 this.2

/-- The pattern `M`-term computed with the nonzero extension of `patM`. -/
theorem mb_mChain_eq_ext (P : PsiData N) {k : ℕ} (σ : Fin k → Bool) (x : Fin k → Fin N)
    (t : ℝ) :
    P.mChain σ x t = Split.chainM t P.S (mbPatMExt P.z σ) (obsSeq P.S x) 1 k := by
  unfold PsiData.mChain
  exact mb_chainM_congr t P.S (fun p hp hp' => (mbPatMExt_of_mem P.z σ hp hp').symm)
    (fun _ _ _ => rfl)

/-!
## Multilinearity in one observable
-/

/-- `Σ_i M̃(…, A_p = B_i, …) = M̃(…, A_p = Σ_i B_i, …)` for `j ≤ p < l`. -/
theorem mb_chainTilde_sum_obs (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ)
    (A : ℕ → Fin N → ℂ) {ι : Type*} (s : Finset ι) (B : ι → Fin N → ℂ) (p n : ℕ) :
    ∀ j l, l - j = n → j ≤ p → p < l →
      ∑ i ∈ s, Split.chainTilde σ S m (update A p (B i)) j l =
        Split.chainTilde σ S m (update A p (∑ i ∈ s, B i)) j l := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j l hn hjp hpl
  have hjl : j < l := lt_of_le_of_lt hjp hpl
  simp_rw [Split.chainTilde_eq σ S m _ j l, ite_eq_left hjl]
  rw [← Matrix.mulVec_sum]
  congr 1
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hjp' : p = j
    · subst hjp'
      have hc : ∀ C : Fin N → ℂ, Split.chainTilde σ S m (update A p C) (p + 1) l =
          Split.chainTilde σ S m A (p + 1) l := fun C =>
        Evol.chainTilde_congr σ S m (l - (p + 1)) (p + 1) l rfl fun q hq _ =>
          update_of_ne (by omega) _ _
      simp only [hc, update_self]
      rw [← Finset.sum_mul]
    · have hj : ∀ C : Fin N → ℂ, update A p C j = A j := fun C => update_of_ne (Ne.symm hjp') _ _
      simp only [hj]
      rw [← Finset.mul_sum, ih (l - (j + 1)) (by omega) (j + 1) l rfl (by omega) hpl]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Ioo.mp hi
    rw [← Finset.smul_sum]
    congr 1
    by_cases hpi : p < i
    · have hc : ∀ C : Fin N → ℂ, Split.chainTilde σ S m (update A p C) i l =
          Split.chainTilde σ S m A i l := fun C =>
        Evol.chainTilde_congr σ S m (l - i) i l rfl fun q hq _ => update_of_ne (by omega) _ _
      simp only [hc]
      rw [← Finset.sum_mul]
      congr 1
      unfold Split.selfEnergy
      rw [← Matrix.mulVec_sum, ih (i - j) (by omega) j i rfl hjp hpi]
    · have hc : ∀ C : Fin N → ℂ, Split.chainTilde σ S m (update A p C) j i =
          Split.chainTilde σ S m A j i := fun C =>
        Evol.chainTilde_congr σ S m (i - j) j i rfl fun q _ hq => update_of_ne (by omega) _ _
      simp only [hc]
      rw [← Finset.mul_sum, ih (l - i) (by omega) i l rfl (by omega) hpl]

/-!
## The VS spectral parameters
-/

theorem mb_zParam_m (z : ℂ) (t : ℝ) : Split.zParam t (semicircleM z) = vsTraj z t := by
  unfold Split.zParam
  have h := (vsFlow_a z t).1
  linear_combination h

theorem mb_zParam_patConj (z : ℂ) (t : ℝ) (b : Bool) :
    Split.zParam t (VS.patConj b (semicircleM z)) = VS.patConj b (vsTraj z t) := by
  cases b
  · simpa [VS.patConj] using mb_zParam_m z t
  · simp only [VS.patConj, ite_true]
    rw [← mb_zParam_m z t]
    unfold Split.zParam
    simp [map_sub, map_div₀, map_neg, map_one, map_mul]

/-- `|z_{j,t} - z_{j+1,t}| = 2η_t` for conjugate neighbours. -/
theorem norm_mb_zParam_sub (z : ℂ) (t : ℝ) {b b' : Bool} (hb : b ≠ b') :
    ‖Split.zParam t (VS.patConj b (semicircleM z)) -
        Split.zParam t (VS.patConj b' (semicircleM z))‖ = 2 * |vsHeight z t| := by
  rw [mb_zParam_patConj, mb_zParam_patConj]
  have hc : ∀ w : ℂ, ‖w - conj w‖ = 2 * |w.im| := by
    intro w
    have : w - conj w = ((2 * w.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
      ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_two]
  cases b <;> cases b' <;> simp only [ne_eq, not_true_eq_false] at hb
  · simp only [VS.patConj, Bool.false_eq_true, ite_false, ite_true]
    rw [hc, vsTraj_im]
  · simp only [VS.patConj, Bool.false_eq_true, ite_false, ite_true]
    rw [← norm_neg, neg_sub, hc, vsTraj_im]

end BlockBand.Native.ErdosRiabov.MBound
