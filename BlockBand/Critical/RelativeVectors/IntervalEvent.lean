module

public import BlockBand.Critical.RelativeVectors.IntervalDet
public import BlockBand.Critical.RelativeVectors.IntervalLog

/-!
# The middle line of the interval bound along the flow, uniformly in time

*Measure:* `flowLaw N a`, `a = rmvStart c N = c - N^{-1/500}`; `H_s = flowMatrix F a ω s`.
*Domain:* fixed `A`, `FreshConstants c r₀ s₀ v₀`, frame rank `r`; every `F` in `FreshClass`,
every frame `V` with `V^*ΓV = I_r`.
*Norm:* the quadratic form of the Hermitian `r × r` matrix `Σ_{i∈S}(z_iz_i^* - Γ_i(s))`
(equivalently its operator norm), `z_i = √N V^*u_i(s)`, `Γ_i(s) = V^*Γ(s, λ_i(s))V`
(`= V^* Im M_s(λ_i)/Im m_s(λ_i) V`, `relGamma_quad_eq`).
*Uniformity:* the constant `C_r = 147 B₄` depends on `(c, r₀, s₀, v₀, r)` only; the event is
uniform over `s ∈ [a, c]` with simple spectrum, all energy intervals `[x, y] ⊂ [E - r₀/4, E + r₀/4]`
(rank intervals in the window are the case `x = λ_{i₁}`, `y = λ_{i₂}`) and all `p ∈ ℂ^r`.

* `relativeInterval_event`: the bound `C_r N^{1-1/100+1/10000} ‖p‖²` outside
  `flowLaw`-probability `N^{-D}`, for every `D`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Set Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Critical.WeightedDensity
open BlockBand.Palm.GoodEvent BlockBand.Palm.MomentFlow BlockBand.Palm.CoarseRelative
open scoped ENNReal NNReal

variable {N r : ℕ}

/-- The mesh precision `δ = v₀L/(1+v₀L) · N^{-(2max(A,1)+3/100)}`. -/
def intDelta (A c s₀ v₀ : ℝ) (N : ℕ) : ℝ :=
  v₀ * lowConst c s₀ v₀ / (1 + v₀ * lowConst c s₀ v₀) * (N : ℝ) ^ (-(2 * max A 1 + 3 / 100))

theorem hundredth_cube {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 3 = (N : ℝ) ^ (-(3 / 100 : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]; norm_num

/-- **The middle line of the interval bound on the mesh good event** (deterministic). -/
theorem interval_of_good {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1)
    {a t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hapos : 0 < a) (has₀ : c - s₀ ≤ a) (hac : a + t = c)
    {K₁ : ℝ} (hK₁ : 0 ≤ K₁) {m : ℕ}
    (hm : K₁ * chainRatio ^ m / (1 - chainRatio) ≤ intDelta A c s₀ v₀ N) (hm2 : (N : ℝ) ≤ 2 ^ m)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (hch : ChainGood K₁ t ω.2)
    (hgood : ∀ j : ℕ, j < 2 ^ m →
      flowNormalized a (a + (j : ℝ) * t / 2 ^ m) ω ∉
        coarseBadSet F E r₀ (a + (j : ℝ) * t / 2 ^ m) (polFrame V)) :
    ∀ s ∈ Icc a c, SimpleSpectrum (flowMatrix F a ω s) →
      ∀ x y : ℝ, E - r₀ / 4 ≤ x → x ≤ y → y ≤ E + r₀ / 4 → ∀ p : Fin r → ℂ,
        |∑ i ∈ Finset.univ.filter (fun i => flowEigenvalue F a ω s i ∈ Icc x y),
            (‖star p ⬝ᵥ frameArray V (flowMatrix F a ω s) i‖ ^ 2 -
              quadForm (freshGamma F s (flowEigenvalue F a ω s i)) (V *ᵥ p))| ≤
          intB4 c r₀ s₀ v₀ r * ((N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) * (dyK N + 2)) * nsq p := by
  intro s hs hss x y hx hxy hy p
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨j, hj, hj1, hj2⟩ := exists_cell ht (sub_nonneg.2 hs.1) (by linarith [hs.2]) m
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hj0 : 0 ≤ (j : ℝ) * t / 2 ^ m := by positivity
  have hjt : (j : ℝ) * t / 2 ^ m ≤ t := by
    rw [div_le_iff₀ h2m]
    have : (j : ℝ) ≤ 2 ^ m := by exact_mod_cast hj.le
    nlinarith
  set σ := a + (j : ℝ) * t / 2 ^ m with hσdef
  have hσpos : 0 < σ := by linarith
  have hσreg : σ ∈ Icc (c - s₀) c := ⟨by linarith, by linarith⟩
  have hsreg : s ∈ Icc (c - s₀) c := ⟨by linarith [hs.1], hs.2⟩
  have hH := BlockBand.Palm.GoodEvent.flowMatrix_isHermitian hC.1 a hω s
  have hH' := BlockBand.Palm.GoodEvent.flowMatrix_isHermitian hC.1 a hω σ
  have hgood' : MeshGood F E r₀ σ (polFrame V) (flowMatrix F a ω σ) := by
    rw [flowMatrix_eq_normalized F a ω hσpos]
    exact meshGood_of_not_coarseBad (hgood j hj)
  set δ := intDelta A c s₀ v₀ N with hδdef
  have hL := lowConst_pos' hK
  have hv0 := hK.2.2.2.2.2
  set vL := v₀ * lowConst c s₀ v₀ with hvL
  have hvL0 : 0 < vL := mul_pos hv0 hL
  set A' := max A 1 with hA'
  have hA'0 : 0 ≤ A' := le_trans zero_le_one (le_max_right _ _)
  have hmod : opB (flowMatrix F a ω s - flowMatrix F a ω σ) ≤ δ := by
    rw [BlockBand.Palm.GoodEvent.flowMatrix_sub, show σ - a = (j : ℝ) * t / 2 ^ m by rw [hσdef]; ring]
    refine (chainGood_modulus hK₁ ht hch m j hj (u := s - a) hj1 hj2).trans (le_trans ?_ hm)
    have hq1 : 0 < 1 - chainRatio := sub_pos.mpr chainRatio_lt_one
    apply div_le_div_of_nonneg_right _ hq1.le
    have hst : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
    have h0 : 0 ≤ K₁ * chainRatio ^ m := by have := chainRatio_pos; positivity
    nlinarith [Real.sqrt_nonneg t]
  have h3 := hundredth_cube hN
  have hfrac : vL / (1 + vL) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hfrac0 : 0 ≤ vL / (1 + vL) := by positivity
  have hpowle : (N : ℝ) ^ (-(2 * A' + 3 / 100)) ≤ (N : ℝ) ^ (-(3 / 100 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  have hΔ' : opB (flowMatrix F a ω s - flowMatrix F a ω σ) ≤ ((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 3 := by
    rw [h3]
    refine hmod.trans ?_
    rw [hδdef, intDelta]
    calc vL / (1 + vL) * (N : ℝ) ^ (-(2 * A' + 3 / 100)) ≤ 1 * (N : ℝ) ^ (-(2 * A' + 3 / 100)) :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ ≤ _ := by rw [one_mul]; exact hpowle
  have hΔ : opB (flowMatrix F a ω s - flowMatrix F a ω σ) *
      ((N : ℝ) ^ (2 * max A 1) / (v₀ * lowConst c s₀ v₀)) ≤ ((N : ℝ) ^ (-(1 / 100 : ℝ))) ^ 3 := by
    rw [h3]
    have hP : 0 ≤ (N : ℝ) ^ (2 * A') / vL := by positivity
    refine (mul_le_mul_of_nonneg_right hmod hP).trans ?_
    rw [hδdef, intDelta]
    have e : vL / (1 + vL) * (N : ℝ) ^ (-(2 * A' + 3 / 100)) * ((N : ℝ) ^ (2 * A') / vL) =
        (N : ℝ) ^ (-(3 / 100 : ℝ)) / (1 + vL) := by
      have : (N : ℝ) ^ (-(2 * A' + 3 / 100)) * (N : ℝ) ^ (2 * A') = (N : ℝ) ^ (-(3 / 100 : ℝ)) := by
        rw [← Real.rpow_add hNr]; ring_nf
      field_simp
      rw [← this]; ring_nf
    rw [e, div_le_iff₀ (by linarith)]
    have : 0 ≤ (N : ℝ) ^ (-(3 / 100 : ℝ)) * vL := by positivity
    linarith
  have hsσ : |s - σ| ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
    have h1 : 0 ≤ s - σ := by rw [hσdef]; linarith
    have h2 : s - σ ≤ t / 2 ^ m := by
      rw [hσdef]
      have : ((j : ℝ) + 1) * t / 2 ^ m = (j : ℝ) * t / 2 ^ m + t / 2 ^ m := by ring
      linarith
    rw [abs_of_nonneg h1]
    refine h2.trans ?_
    have h3' : t / 2 ^ m ≤ 1 / N := by
      rw [div_le_div_iff₀ h2m hNr]; nlinarith
    refine h3'.trans ?_
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  have hb := fun x hx => interval_time_bounds hN hK hC hV hsreg hσreg hH hH' hgood' hΔ hΔ' hsσ x hx
  exact interval_det hN hK hC hV hsreg hss (fun x hx => (hb x hx).1) (fun x hx => (hb x hx).2.1)
    (fun x hx => (hb x hx).2.2) (dyK_spec hN).1 (dyK_spec hN).2 hx hxy hy p

/-- Polynomial bookkeeping of the union bound. -/
theorem interval_numeric (A' D Qc : ℝ) (hA' : 0 ≤ A') : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    2 * (1 / 2 : ℝ) ^ N + (1 + Qc * (N : ℝ) ^ (8 * A' + 12 / 100) + 2 * N) *
      (N : ℝ) ^ (-(D + 8 * A' + 2)) ≤ (N : ℝ) ^ (-D) := by
  have e1 := ev_exp_le 8 0 (-D)
  have e2 := ev_poly_le 4 (-(D + 8 * A' + 2)) (-D) (by linarith)
  have e3 := ev_poly_le (4 * Qc) (-D - 2 + 12 / 100) (-D) (by linarith)
  have e4 := ev_poly_le 8 (-D - 1 - 8 * A') (-D) (by linarith)
  obtain ⟨N₀, hN₀⟩ :=
    (e1.and (e2.and (e3.and (e4.and (eventually_ge_atTop 1))))).exists_forall_of_atTop
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3, h4, hN1⟩ := hN₀ N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.rpow_zero, mul_one] at h1
  have e : (1 + Qc * (N : ℝ) ^ (8 * A' + 12 / 100) + 2 * N) * (N : ℝ) ^ (-(D + 8 * A' + 2)) =
      (N : ℝ) ^ (-(D + 8 * A' + 2)) + Qc * (N : ℝ) ^ (-D - 2 + 12 / 100) +
        2 * (N : ℝ) ^ (-D - 1 - 8 * A') := by
    have a1 : (N : ℝ) ^ (8 * A' + 12 / 100) * (N : ℝ) ^ (-(D + 8 * A' + 2)) =
        (N : ℝ) ^ (-D - 2 + 12 / 100) := by
      rw [← Real.rpow_add hNr]; congr 1; ring
    have a2 : (N : ℝ) * (N : ℝ) ^ (-(D + 8 * A' + 2)) = (N : ℝ) ^ (-D - 1 - 8 * A') := by
      rw [show (N : ℝ) * (N : ℝ) ^ (-(D + 8 * A' + 2)) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(D + 8 * A' + 2)) by rw [Real.rpow_one],
        ← Real.rpow_add hNr]
      congr 1; ring
    calc (1 + Qc * (N : ℝ) ^ (8 * A' + 12 / 100) + 2 * N) * (N : ℝ) ^ (-(D + 8 * A' + 2))
        = (N : ℝ) ^ (-(D + 8 * A' + 2)) +
            Qc * ((N : ℝ) ^ (8 * A' + 12 / 100) * (N : ℝ) ^ (-(D + 8 * A' + 2))) +
            2 * ((N : ℝ) * (N : ℝ) ^ (-(D + 8 * A' + 2))) := by ring
      _ = _ := by rw [a1, a2]
  rw [e]
  linarith

/-- **The middle line of the interval bound, uniformly along the flow.** See the module
docstring. -/
theorem relativeInterval_event (hCR : CoarseRelativeContract) (hLp : GaussianLpGradient)
    {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) (r : ℕ) :
    ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
    ∀ V : Matrix (Fin N) (Fin r) ℂ, Vᴴ * freshGamma F c E * V = 1 →
      flowLaw N (rmvStart c N) {ω | ¬ ∀ s ∈ Icc (rmvStart c N) c,
        SimpleSpectrum (flowMatrix F (rmvStart c N) ω s) →
        ∀ x y : ℝ, E - r₀ / 4 ≤ x → x ≤ y → y ≤ E + r₀ / 4 → ∀ p : Fin r → ℂ,
          |∑ i ∈ Finset.univ.filter (fun i => flowEigenvalue F (rmvStart c N) ω s i ∈ Icc x y),
              (‖star p ⬝ᵥ frameArray V (flowMatrix F (rmvStart c N) ω s) i‖ ^ 2 -
                quadForm (freshGamma F s (flowEigenvalue F (rmvStart c N) ω s i)) (V *ᵥ p))| ≤
            147 * intB4 c r₀ s₀ v₀ r * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ) * nsq p} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro D
  have hK0 := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK0
  obtain ⟨K₁, hK₁, hCE⟩ := chain_event hLp
  have hq1 : 0 < 1 - chainRatio := sub_pos.mpr chainRatio_lt_one
  have hL := lowConst_pos' hK
  set A' := max A 1 with hA'
  have hA'0 : 0 ≤ A' := le_trans zero_le_one (le_max_right _ _)
  set vL := v₀ * lowConst c s₀ v₀ with hvL
  have hvL0 : 0 < vL := mul_pos hv0 hL
  set Qc := 2 * (K₁ / (1 - chainRatio)) ^ 4 * ((1 + vL) / vL) ^ 4 with hQc
  have hQc0 : 0 ≤ Qc := by positivity
  set D' := D + 8 * A' + 2 with hD'
  obtain ⟨Ncr, hNcr⟩ := hCR A c r₀ s₀ v₀ hK 1 D'
  obtain ⟨Nnum, hNnum⟩ := interval_numeric A' D Qc hA'0
  have ht0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 500 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nt, hNt⟩ := (eventually_atTop.1 (ht0.eventually (gt_mem_nhds hs0)))
  refine ⟨max (max Ncr Nnum) (max Nt (max 8 (4 * r ^ 2))), ?_⟩
  intro N hN F E hC V hV
  have hNcr' := hNcr N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have hnum := hNnum N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have htN := hNt N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have h8 : 8 ≤ N := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hr2 : 4 * r ^ 2 ≤ N := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set t := (N : ℝ) ^ (-(1 / 500 : ℝ)) with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos hNr _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN0) (by norm_num)
  have ha : rmvStart c N = c - t := rfl
  rw [ha]
  set a := c - t with hadef
  have hapos : 0 < a := by linarith
  have has₀ : c - s₀ ≤ a := by linarith
  have hac : a + t = c := by ring
  set δ := intDelta A c s₀ v₀ N with hδ
  have hδpos : 0 < δ := by rw [hδ, intDelta]; positivity
  obtain ⟨m₁, hm₁, h2m₁⟩ := exists_mesh_level hK₁ hδpos
  set m₂ := Nat.log 2 N + 1 with hm₂
  have hm₂N : N < 2 ^ m₂ := Nat.lt_pow_succ_log_self (by norm_num) N
  have hm₂le : 2 ^ m₂ ≤ 2 * N := by
    rw [hm₂, pow_succ]
    have := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    omega
  set m := max m₁ m₂ with hmdef
  have hm : K₁ * chainRatio ^ m / (1 - chainRatio) ≤ δ := by
    refine le_trans ?_ hm₁
    apply div_le_div_of_nonneg_right _ hq1.le
    apply mul_le_mul_of_nonneg_left _ hK₁.le
    exact pow_le_pow_of_le_one chainRatio_pos.le (chainRatio_lt_one.le) (le_max_left _ _)
  have hm2 : (N : ℝ) ≤ 2 ^ m := by
    have : N ≤ 2 ^ m := hm₂N.le.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
    exact_mod_cast this
  have h2m : (2 : ℝ) ^ m ≤ 2 ^ m₁ + 2 * N := by
    rcases le_total m₁ m₂ with h | h
    · rw [hmdef, max_eq_right h]
      have : ((2 ^ m₂ : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hm₂le
      push_cast at this
      have : (0 : ℝ) ≤ 2 ^ m₁ := by positivity
      linarith
    · rw [hmdef, max_eq_left h]
      have : (0 : ℝ) ≤ 2 * N := by positivity
      linarith
  have hQ : ((polFrame V).card : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    refine (polFrame_card_le V).trans ?_
    exact_mod_cast hr2
  -- covering
  have hsub : {ω : FlowSample N | ¬ ∀ s ∈ Icc a c, SimpleSpectrum (flowMatrix F a ω s) →
        ∀ x y : ℝ, E - r₀ / 4 ≤ x → x ≤ y → y ≤ E + r₀ / 4 → ∀ p : Fin r → ℂ,
          |∑ i ∈ Finset.univ.filter (fun i => flowEigenvalue F a ω s i ∈ Icc x y),
              (‖star p ⬝ᵥ frameArray V (flowMatrix F a ω s) i‖ ^ 2 -
                quadForm (freshGamma F s (flowEigenvalue F a ω s i)) (V *ᵥ p))| ≤
            147 * intB4 c r₀ s₀ v₀ r * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ) * nsq p} ⊆
      ({ω : FlowSample N | ¬ ω.1.IsHermitian} ∪ {ω | ¬ ChainGood K₁ t ω.2}) ∪
        ⋃ j ∈ Finset.range (2 ^ m), {ω | flowNormalized a (a + (j : ℝ) * t / 2 ^ m) ω ∈
          coarseBadSet F E r₀ (a + (j : ℝ) * t / 2 ^ m) (polFrame V)} := by
    intro ω hω
    by_contra hcon
    apply hω
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
      Finset.mem_range] at hcon
    obtain ⟨⟨hH, hCh⟩, hJ⟩ := hcon
    push Not at hH hCh
    intro s hs hss x y hx hxy hy p
    refine (interval_of_good hN0 hK hC hV ht ht1 hapos has₀ hac hK₁.le hm hm2 hH hCh
      (fun j hj => hJ j hj) s hs hss x y hx hxy hy p).trans ?_
    have hB4 : 0 ≤ intB4 c r₀ s₀ v₀ r := by
      have := dysonGammaConst_nonneg hK
      have := dysonShiftConst_nonneg hK
      have := (gammaCompConst_pos hK).le
      unfold intB4 intR intB1 intB2 intB3
      have : 0 ≤ max r₀ 1 := le_trans zero_le_one (le_max_right _ _)
      positivity
    have := nhK_le hN0
    have hp0 := nsq_nonneg p
    calc intB4 c r₀ s₀ v₀ r * ((N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) * (dyK N + 2)) * nsq p
        ≤ intB4 c r₀ s₀ v₀ r * (147 * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ)) * nsq p := by
          apply mul_le_mul_of_nonneg_right _ hp0
          exact mul_le_mul_of_nonneg_left this hB4
      _ = _ := by ring
  refine (measure_mono hsub).trans ?_
  refine ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _))).trans ?_
  have hS : ∀ j ∈ Finset.range (2 ^ m), flowLaw N a {ω | flowNormalized a (a + (j : ℝ) * t / 2 ^ m)
      ω ∈ coarseBadSet F E r₀ (a + (j : ℝ) * t / 2 ^ m) (polFrame V)} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h2m0 : (0 : ℝ) < 2 ^ m := by positivity
    have hjt : (j : ℝ) * t / 2 ^ m ≤ t := by
      rw [div_le_iff₀ h2m0]
      have : (j : ℝ) ≤ 2 ^ m := by exact_mod_cast hj.le
      nlinarith
    have hj0 : 0 ≤ (j : ℝ) * t / 2 ^ m := by positivity
    have hsja : a ≤ a + (j : ℝ) * t / 2 ^ m := le_add_of_nonneg_right hj0
    have hsjreg : a + (j : ℝ) * t / 2 ^ m ∈ Icc (c - s₀) c := ⟨by linarith, by linarith⟩
    refine (flowLaw_preimage_normalized_le hN0 hapos hsja _).trans ?_
    exact hNcr' F E hC _ hsjreg (polFrame V) hQ
  refine (add_le_add (add_le_add (le_of_eq (flowLaw_not_hermitian a)) (hCE N h8 a t ht))
    (Finset.sum_le_sum hS)).trans ?_
  rw [Finset.sum_const, Finset.card_range, zero_add, nsmul_eq_mul]
  have hc2m : ((2 ^ m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ m) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [hc2m, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ hnum
  have hδinv : (δ⁻¹) ^ 4 = ((1 + vL) / vL) ^ 4 * (N : ℝ) ^ (8 * A' + 12 / 100) := by
    have e1 : δ⁻¹ = (1 + vL) / vL * (N : ℝ) ^ (2 * A' + 3 / 100) := by
      rw [hδ, intDelta, mul_inv, Real.rpow_neg hNr.le, inv_inv, inv_div]
    have e2 : ((N : ℝ) ^ (2 * A' + 3 / 100)) ^ 4 = (N : ℝ) ^ (8 * A' + 12 / 100) := by
      rw [← Real.rpow_mul_natCast hNr.le]; congr 1; push_cast; ring
    rw [e1, mul_pow, e2]
  have h2m' : (2 : ℝ) ^ m ≤ 1 + Qc * (N : ℝ) ^ (8 * A' + 12 / 100) + 2 * N := by
    refine h2m.trans ?_
    have : (2 : ℝ) ^ m₁ ≤ 1 + Qc * (N : ℝ) ^ (8 * A' + 12 / 100) := by
      refine h2m₁.trans (le_of_eq ?_)
      rw [hδinv, hQc]; ring
    linarith
  have := mul_le_mul_of_nonneg_right h2m' (Real.rpow_nonneg hNr.le (-D'))
  linarith

end BlockBand.Critical.RelativeVectors
