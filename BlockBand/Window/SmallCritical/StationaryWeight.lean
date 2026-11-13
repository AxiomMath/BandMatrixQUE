module

public import BlockBand.Window.SmallCritical.MarkedFatou
public import BlockBand.Model.Construction.MarkedTranslationLaw

/-!
# Uniformity in the spectral weight from spectral stationarity

For a law `P` on marked point measures invariant under every global spectral translation
(`globalMarkedTranslationLaw t P = P`, the translation clause of the stationarity proposition,
`criticalSequence_marked_weakLimit_spectral_law_invariant`), a continuous mark functional
`g ≥ 0` and `Λ(w) = E_P ∫⁻ ofReal (w(u) g(ν)) dξ(u,ν)`:

* `weightFunctional_translate`: `Λ(w(· + s)) = Λ(w)`;
* `weightFunctional_le_four`: for every continuous compactly supported `w ≥ 0` with `∫ w = 1`
  and every continuous `ψ ≥ 0` with compact support and `ψ ≥ 1` on `[0,1]`,
  `Λ(w) ≤ 4 Λ(ψ)`.

Proof: average `K` translates of `w` over a length `L = 2R + 2` (`supp w ⊆ [-R,R]`); uniform
continuity bounds the Riemann average by `2/L` on `[-R, R+L]`, and `⌊2R+L⌋ + 1` unit
translates of `ψ` cover that interval. Everything is a finite sum; no Fubini over `P`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction
open scoped ENNReal NNReal

attribute [local instance] massProfile_opensMeasurableSpace

/-- `Λ_g(w) = E_P Σ_α w(u_α) g(ν_α)`, as a lower integral. -/
def weightFunctional (P : ProbabilityMeasure MarkedPointMeasure) (g : MassProfile → ℝ)
    (w : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (w x.1 * g x.2) ∂ξ.marked.measure ∂(P : Measure MarkedPointMeasure)

/-- `w(u) g(ν)` has compact support on `ℝ × P(𝕋)` (the mark space is compact). -/
theorem hasCompactSupport_prodTest {w : ℝ → ℝ} (hws : HasCompactSupport w)
    (g : MassProfile → ℝ) :
    HasCompactSupport (fun x : MarkedSpectralSpace => w x.1 * g x.2) := by
  have h1 : HasCompactSupport (fun x : MarkedSpectralSpace => w x.1) := by
    rw [HasCompactSupport]
    apply IsCompact.of_isClosed_subset (hws.isCompact.prod isCompact_univ) (isClosed_tsupport _)
    apply closure_minimal _ ((isClosed_tsupport w).prod isClosed_univ)
    intro x hx
    exact ⟨subset_tsupport _ hx, trivial⟩
  exact h1.mul_right (f' := fun x : MarkedSpectralSpace => g x.2)

theorem continuous_prodTest {w : ℝ → ℝ} (hwc : Continuous w) {g : MassProfile → ℝ}
    (hg : Continuous g) : Continuous (fun x : MarkedSpectralSpace => w x.1 * g x.2) :=
  (hwc.comp continuous_fst).mul (hg.comp continuous_snd)

theorem prodTest_nonneg {w : ℝ → ℝ} (hw0 : ∀ x, 0 ≤ w x) {g : MassProfile → ℝ}
    (hg0 : ∀ ν, 0 ≤ g ν) (x : MarkedSpectralSpace) : 0 ≤ w x.1 * g x.2 :=
  mul_nonneg (hw0 _) (hg0 _)

/-- Monotonicity in the weight. -/
theorem weightFunctional_mono (P : ProbabilityMeasure MarkedPointMeasure)
    {g : MassProfile → ℝ} (hg0 : ∀ ν, 0 ≤ g ν) {w w' : ℝ → ℝ} (h : ∀ u, w u ≤ w' u) :
    weightFunctional P g w ≤ weightFunctional P g w' := by
  unfold weightFunctional
  refine lintegral_mono fun ξ => lintegral_mono fun x => ?_
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (h _) (hg0 _))

/-- Homogeneity in the weight. -/
theorem weightFunctional_const_mul (P : ProbabilityMeasure MarkedPointMeasure)
    (g : MassProfile → ℝ) (w : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    weightFunctional P g (fun u => c * w u) = ENNReal.ofReal c * weightFunctional P g w := by
  unfold weightFunctional
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ξ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul hc, mul_assoc]

/-- Superadditivity of lower integrals over a finite family (no measurability). -/
theorem sum_lintegral_le_lintegral_sum {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    calc (∫⁻ a, f i a ∂μ) + ∑ j ∈ s, ∫⁻ a, f j a ∂μ ≤
        (∫⁻ a, f i a ∂μ) + ∫⁻ a, ∑ j ∈ s, f j a ∂μ := by gcongr
      _ ≤ ∫⁻ a, (f i a + ∑ j ∈ s, f j a) ∂μ := le_lintegral_add _ _
      _ = ∫⁻ a, ∑ j ∈ insert i s, f j a ∂μ := by
        congr 1; funext a; rw [Finset.sum_insert hi]

/-- Superadditivity in the weight (nonnegative weights and marks). -/
theorem sum_weightFunctional_le (P : ProbabilityMeasure MarkedPointMeasure)
    {g : MassProfile → ℝ} (hg0 : ∀ ν, 0 ≤ g ν) {ι : Type*} (s : Finset ι)
    (w : ι → ℝ → ℝ) (hw0 : ∀ i u, 0 ≤ w i u) :
    ∑ i ∈ s, weightFunctional P g (w i) ≤ weightFunctional P g (fun u => ∑ i ∈ s, w i u) := by
  unfold weightFunctional
  refine (sum_lintegral_le_lintegral_sum _ s _).trans (lintegral_mono fun ξ => ?_)
  refine (sum_lintegral_le_lintegral_sum _ s _).trans (lintegral_mono fun x => ?_)
  rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw0 i _) (hg0 _))]

/-- Additivity in the weight for continuous compactly supported nonnegative weights. -/
theorem weightFunctional_sum (P : ProbabilityMeasure MarkedPointMeasure)
    {g : MassProfile → ℝ} (hg : Continuous g) (hg0 : ∀ ν, 0 ≤ g ν) {ι : Type*} (s : Finset ι)
    (w : ι → ℝ → ℝ) (hwc : ∀ i, Continuous (w i)) (hws : ∀ i, HasCompactSupport (w i))
    (hw0 : ∀ i u, 0 ≤ w i u) :
    weightFunctional P g (fun u => ∑ i ∈ s, w i u) = ∑ i ∈ s, weightFunctional P g (w i) := by
  unfold weightFunctional
  have hin : ∀ ξ : MarkedPointMeasure,
      ∫⁻ x, ENNReal.ofReal ((∑ i ∈ s, w i x.1) * g x.2) ∂ξ.marked.measure =
        ∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (w i x.1 * g x.2) ∂ξ.marked.measure := by
    intro ξ
    rw [← lintegral_finsetSum]
    · refine lintegral_congr fun x => ?_
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw0 i _) (hg0 _))]
    · intro i _
      exact ENNReal.measurable_ofReal.comp (continuous_prodTest (hwc i) hg).measurable
  simp_rw [hin]
  rw [lintegral_finsetSum]
  intro i _
  exact measurable_markedLIntegral (continuous_prodTest (hwc i) hg)
    (hasCompactSupport_prodTest (hws i) g) (prodTest_nonneg (hw0 i) hg0)

/-- Translation invariance of `Λ` under a spectrally stationary law. -/
theorem weightFunctional_translate (P : ProbabilityMeasure MarkedPointMeasure)
    (hstat : ∀ t : ℝ, globalMarkedTranslationLaw t P = P)
    {g : MassProfile → ℝ} (hg : Continuous g) (hg0 : ∀ ν, 0 ≤ g ν)
    {w : ℝ → ℝ} (hwc : Continuous w) (hws : HasCompactSupport w) (hw0 : ∀ u, 0 ≤ w u) (s : ℝ) :
    weightFunctional P g (fun u => w (u + s)) = weightFunctional P g w := by
  conv_rhs => rw [weightFunctional, ← hstat s, globalMarkedTranslationLaw_measure]
  rw [lintegral_map (measurable_markedLIntegral (continuous_prodTest hwc hg)
    (hasCompactSupport_prodTest hws g) (prodTest_nonneg hw0 hg0))
    (measurable_globalMarkedTranslation s)]
  unfold weightFunctional
  refine lintegral_congr fun ξ => ?_
  have hm : Measurable (fun x : MarkedSpectralSpace => ENNReal.ofReal (w x.1 * g x.2)) :=
    ENNReal.measurable_ofReal.comp (continuous_prodTest hwc hg).measurable
  rw [globalMarkedTranslation_marked_measure, lintegral_map hm
    (measurable_gaussianMarkedLocationTranslate s)]
  rfl

/-- One Riemann cell: `h w(a) ≤ ∫_{t₀}^{t₀+h} w(u - t) dt + h δ` when `w` varies by at most `δ`
over distance `h` and `a = u - t₀`. -/
theorem riemann_cell_le {w : ℝ → ℝ} (hwc : Continuous w) {h δ : ℝ} (hh : 0 ≤ h)
    (hunif : ∀ x y, |x - y| ≤ h → w x ≤ w y + δ) (u t₀ : ℝ) :
    h * w (u - t₀) ≤ (∫ t in t₀..t₀ + h, w (u - t)) + h * δ := by
  have hc : Continuous (fun t => w (u - t)) := hwc.comp (continuous_const.sub continuous_id)
  have hm := intervalIntegral.integral_mono_on (by linarith : t₀ ≤ t₀ + h)
    (continuous_const.intervalIntegrable (μ := volume) _ _)
    ((hc.add continuous_const).intervalIntegrable (μ := volume) _ _)
    (f := fun _ => w (u - t₀)) (g := fun t => w (u - t) + δ) (fun t ht => by
      apply hunif
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const] at hm
  simp only [add_sub_cancel_left, smul_eq_mul] at hm
  linarith

/-- Riemann average bound: if `w ≥ 0`, `∫ w = 1` and `w` varies by at most `δ` over
distance `L/K`, then `K⁻¹ Σ_{k<K} w(u - kL/K) ≤ (1 + Lδ)/L` for every `u`. -/
theorem riemann_avg_le {w : ℝ → ℝ} (hwc : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (hwi : Integrable w) (hw1 : ∫ x, w x = 1) {L δ : ℝ} (hL : 0 < L) {K : ℕ} (hK : 0 < K)
    (hunif : ∀ x y, |x - y| ≤ L / K → w x ≤ w y + δ) (u : ℝ) :
    (1 / (K : ℝ)) * ∑ k ∈ Finset.range K, w (u - k * (L / K)) ≤ (1 + L * δ) / L := by
  set h : ℝ := L / K with hh
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hh0 : 0 < h := div_pos hL hK'
  have hc : Continuous (fun t => w (u - t)) := hwc.comp (continuous_const.sub continuous_id)
  have hcell : ∀ k ∈ Finset.range K, h * w (u - k * h) ≤
      (∫ t in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h, w (u - t)) + h * δ := by
    intro k _
    have := riemann_cell_le hwc hh0.le hunif u (k * h)
    rwa [show ((k + 1 : ℕ) : ℝ) * h = k * h + h by push_cast; ring]
  have hsum := Finset.sum_le_sum hcell
  rw [Finset.sum_add_distrib, intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * h) (fun k _ => hc.intervalIntegrable _ _),
    ← Finset.mul_sum] at hsum
  simp only [Nat.cast_zero, zero_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hKh : (K : ℝ) * h = L := by rw [hh]; field_simp
  rw [hKh] at hsum
  have hint : (∫ t in (0 : ℝ)..L, w (u - t)) ≤ 1 := by
    rw [intervalIntegral.integral_of_le hL.le, ← hw1,
      ← integral_sub_left_eq_self w volume u]
    exact setIntegral_le_integral (hwi.comp_sub_left u) (Eventually.of_forall fun t => hw0 _)
  have e : (K : ℝ) * (h * δ) = L * δ := by rw [← mul_assoc, hKh]
  rw [e] at hsum
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hK' hL]
  have : h * ∑ k ∈ Finset.range K, w (u - k * h) ≤ 1 + L * δ := by linarith
  calc (∑ k ∈ Finset.range K, w (u - k * h)) * L =
      (K : ℝ) * (h * ∑ k ∈ Finset.range K, w (u - k * h)) := by rw [← hKh]; ring
    _ ≤ (K : ℝ) * (1 + L * δ) := by gcongr
    _ = (1 + L * δ) * K := by ring

/-- Uniformity in the weight: under a spectrally stationary law, for a continuous mark
functional `g ≥ 0`, every continuous compactly supported `w ≥ 0` with `∫ w = 1` satisfies
`Λ(w) ≤ 4 Λ(ψ)` for any continuous compactly supported `ψ ≥ 0` with `ψ ≥ 1` on `[0,1]`. -/
theorem weightFunctional_le_four (P : ProbabilityMeasure MarkedPointMeasure)
    (hstat : ∀ t : ℝ, globalMarkedTranslationLaw t P = P)
    {g : MassProfile → ℝ} (hg : Continuous g) (hg0 : ∀ ν, 0 ≤ g ν)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ u, 0 ≤ ψ u)
    (hψ1 : ∀ u ∈ Icc (0 : ℝ) 1, 1 ≤ ψ u)
    {w : ℝ → ℝ} (hwc : Continuous w) (hws : HasCompactSupport w) (hw0 : ∀ u, 0 ≤ w u)
    (hw1 : ∫ x, w x = 1) :
    weightFunctional P g w ≤ 4 * weightFunctional P g ψ := by
  -- support radius
  obtain ⟨R₀, hR₀⟩ := (hws.isCompact.isBounded).subset_closedBall (0 : ℝ)
  set R : ℝ := max R₀ 0 with hR
  have hR0 : 0 ≤ R := le_max_right _ _
  have hsupp : ∀ x, w x ≠ 0 → |x| ≤ R := by
    intro x hx
    have := hR₀ (subset_tsupport w hx)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set L : ℝ := 2 * R + 2 with hL
  have hL0 : 0 < L := by positivity
  -- uniform continuity at tolerance `1/L`
  obtain ⟨h₀, hh₀, hdist⟩ := Metric.uniformContinuous_iff.mp
    (hws.uniformContinuous_of_continuous hwc) (1 / L) (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_gt (L / h₀)
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := lt_trans (div_pos hL0 hh₀) hK
    exact_mod_cast this
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hLK : L / K < h₀ := by
    rw [div_lt_iff₀ hK']; rw [div_lt_iff₀ hh₀] at hK; linarith
  have hunif : ∀ x y, |x - y| ≤ L / K → w x ≤ w y + 1 / L := by
    intro x y hxy
    have := hdist (show dist x y < h₀ by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport hws
  set h : ℝ := L / K with hh
  -- the average of translates
  let avg : ℝ → ℝ := fun u => ∑ k ∈ Finset.range K, (1 / (K : ℝ)) * w (u - k * h)
  have hstep1 : weightFunctional P g w ≤ weightFunctional P g avg := by
    have heach : ∀ k ∈ Finset.range K,
        weightFunctional P g (fun u => (1 / (K : ℝ)) * w (u - k * h)) =
          ENNReal.ofReal (1 / (K : ℝ)) * weightFunctional P g w := by
      intro k _
      rw [weightFunctional_const_mul P g _ (by positivity)]
      congr 1
      simpa only [sub_eq_add_neg] using
        weightFunctional_translate P hstat hg hg0 hwc hws hw0 (-(k * h))
    have hsup := sum_weightFunctional_le P hg0 (Finset.range K)
      (fun k u => (1 / (K : ℝ)) * w (u - k * h)) (fun k u => mul_nonneg (by positivity) (hw0 _))
    rw [Finset.sum_congr rfl heach, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← mul_assoc] at hsup
    have hone : (K : ℝ≥0∞) * ENNReal.ofReal (1 / (K : ℝ)) = 1 := by
      rw [one_div, ENNReal.ofReal_inv_of_pos hK', ENNReal.ofReal_natCast]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast hKpos.ne') (ENNReal.natCast_ne_top K)
    rw [hone, one_mul] at hsup
    exact hsup
  -- the covering by unit translates of `ψ`
  set J : ℕ := ⌊2 * R + L⌋₊ with hJ
  let χ : ℝ → ℝ := fun u => ∑ j ∈ Finset.range (J + 1), ψ (u + (R - j))
  have hpt : ∀ u, avg u ≤ 2 / L * χ u := by
    intro u
    by_cases hu : u ∈ Icc (-R) (R + L)
    · have hav : avg u ≤ 2 / L := by
        have := riemann_avg_le hwc hw0 hwi hw1 hL0 hKpos hunif u
        have h2 : (1 + L * (1 / L)) / L = 2 / L := by field_simp; ring
        rw [h2] at this
        calc avg u = (1 / (K : ℝ)) * ∑ k ∈ Finset.range K, w (u - k * (L / K)) := by
              rw [Finset.mul_sum]
          _ ≤ 2 / L := this
      have hχ : 1 ≤ χ u := by
        set v : ℝ := u + R with hv
        have hv0 : 0 ≤ v := by linarith [hu.1]
        have hvJ : ⌊v⌋₊ ≤ J := Nat.floor_mono (by linarith [hu.2])
        have hmem : ⌊v⌋₊ ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
        have hle : ψ (u + (R - ⌊v⌋₊)) ≤ χ u :=
          Finset.single_le_sum (f := fun j : ℕ => ψ (u + (R - j))) (fun j _ => hψ0 _) hmem
        refine le_trans (hψ1 _ ⟨?_, ?_⟩) hle
        · have := Nat.floor_le hv0; linarith
        · have := Nat.lt_floor_add_one v; linarith
      calc avg u ≤ 2 / L := hav
        _ = 2 / L * 1 := (mul_one _).symm
        _ ≤ 2 / L * χ u := by gcongr
    · have hzero : avg u = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        by_contra hne
        have hwk : w (u - k * h) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
        have hb := hsupp _ hwk
        rw [abs_le] at hb
        have hk1 : (k : ℝ) * h ≤ L := by
          have : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_range.mp hk).le
          calc (k : ℝ) * h ≤ K * h := by gcongr
            _ = L := by rw [hh]; field_simp
        have hk0 : 0 ≤ (k : ℝ) * h := by positivity
        exact hu ⟨by linarith [hb.1], by linarith [hb.2]⟩
      rw [hzero]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hψ0 _)
  have hstep2 : weightFunctional P g avg ≤ weightFunctional P g (fun u => 2 / L * χ u) :=
    weightFunctional_mono P hg0 hpt
  have hstep3 : weightFunctional P g (fun u => 2 / L * χ u) =
      ENNReal.ofReal (2 / L) * ((J + 1 : ℕ) * weightFunctional P g ψ) := by
    rw [weightFunctional_const_mul P g χ (by positivity)]
    congr 1
    rw [weightFunctional_sum P hg hg0 (Finset.range (J + 1)) (fun (j : ℕ) u => ψ (u + (R - j)))
      (fun j => hψc.comp (continuous_id.add continuous_const))
      (fun j => by
        have := hψs.comp_homeomorph (Homeomorph.addRight ((R - j : ℝ)))
        exact this)
      (fun j u => hψ0 _)]
    rw [Finset.sum_congr rfl (fun (j : ℕ) _ =>
      weightFunctional_translate P hstat hg hg0 hψc hψs hψ0 (R - j)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hfin : ENNReal.ofReal (2 / L) * ((J + 1 : ℕ) : ℝ≥0∞) ≤ 4 := by
    have hJle : (J : ℝ) ≤ 2 * R + L := Nat.floor_le (by positivity)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num]
    apply ENNReal.ofReal_le_ofReal
    rw [div_mul_eq_mul_div, div_le_iff₀ hL0]
    push_cast
    nlinarith
  calc weightFunctional P g w ≤ weightFunctional P g avg := hstep1
    _ ≤ _ := hstep2
    _ = ENNReal.ofReal (2 / L) * ((J + 1 : ℕ) * weightFunctional P g ψ) := hstep3
    _ = (ENNReal.ofReal (2 / L) * ((J + 1 : ℕ) : ℝ≥0∞)) * weightFunctional P g ψ := by ring
    _ ≤ 4 * weightFunctional P g ψ := by gcongr

end BlockBand.Window.SmallCritical
