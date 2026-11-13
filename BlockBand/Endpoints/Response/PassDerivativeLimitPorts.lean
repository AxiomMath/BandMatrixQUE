module

public import BlockBand.Endpoints.Response.PassDerivativeLimitNear
public import BlockBand.Endpoints.Response.PassDerivativeLimitReversal

/-!
# The critical derivative of each port along moving energies

* `nearPort_tendsto`: `lim_W E D₀(p) = -4πρ(E) E_{x,y}[1{σ₀ ≤ τ}∫_0^τ p(τ-s) R_s ds]`;
* `farPort_tendsto`: `lim_W E D₁(q) = -4πρ(E) E_{x,y}[1{σ₀ ≤ τ}∫_0^τ q(s) R_s ds]`
  ("reversing the layer order replaces `q(s)` by `q(τ-s)`"): the far port of a
  sample is the near port of the reversed sample (`portDeriv_one_revPath`), the reversal
  preserves the law (`growthPathLaw_map_revPath`), and the reversed grid profile
  `q((n+1)/W - ·)` is uniformly close to `q(τ - ·)` on the grid, which costs `o(1)` by
  additivity and the clock moment (`abs_integral_portDeriv_small`).
Both values are `ResponseData`: every realization of the boundary dual has an integrable response
with that expectation.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

theorem ResponseData.unique {D0 τ x y v₁ v₂ : ℝ} {g : ℝ → ℝ}
    (hex : HasBoundaryDualProcess D0 ![x] ![y]) (h₁ : ResponseData D0 τ g x y v₁)
    (h₂ : ResponseData D0 τ g x y v₂) : v₁ = v₂ := by
  obtain ⟨Ω, m, 𝓖, P, N, X, Y, hR⟩ := hex
  rw [← (h₁ Ω m 𝓖 P N X Y hR).2, (h₂ Ω m 𝓖 P N X Y hR).2]

theorem transportD0_pos {b E : ℝ} (hb0 : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) :
    0 < transportD0 b E := by
  unfold transportD0
  have : 0 < 4 - E ^ 2 := by nlinarith
  positivity

theorem absorptionConst_ne_zero {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    -(4 * Real.pi * Parameters.semicircleDensity E) ≠ 0 := by
  have := semicircleDensity_pos' hE1 hE2
  have : 0 < 4 * Real.pi * Parameters.semicircleDensity E := by positivity
  linarith

/-!
### Near port, general nonnegative profile
-/

theorem nearPort_tendsto (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hInvU : PathFractionalInverseEnergyUniform) {b E x y τ Ce : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hxy : ¬(x = 0 ∧ y = 0)) (hτ : 0 < τ) {j : ℕ → ℕ}
    (hj : Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ)) {p : ℝ → ℝ} (hpc : Continuous p)
    (hp0 : ∀ t, 0 ≤ p t) {Q : ℝ} (hpQ : ∀ t, p t ≤ Q) {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) :
    ∃ v, ResponseData (transportD0 b E) τ (fun s => p (τ - s)) x y v ∧
      Tendsto (fun W : ℕ => ∫ ω, portDeriv b (e W) x y W (j W) p 0 ω ∂growthPathLaw W b) atTop
        (𝓝 (-(4 * Real.pi * Parameters.semicircleDensity E) * v)) := by
  have hD0 := transportD0_pos hb0 hE1 hE2
  have hstart := isDualStart_one hx hy0 hy1.le hxy
  obtain ⟨Ω₀, m₀, 𝓖₀, P₀, N₀, X₀, Y₀, hR₀⟩ := hBdry.exists_ _ hD0 x y hstart
  have pos : ∀ p' : ℝ → ℝ, Continuous p' → (∀ t, 1 ≤ p' t) → ∀ Q' : ℝ, (∀ t, p' t ≤ Q') →
      ∃ v, ResponseData (transportD0 b E) τ (fun s => p' (τ - s)) x y v ∧
        Tendsto (fun W : ℕ => ∫ ω, portDeriv b (e W) x y W (j W) p' 0 ω ∂growthPathLaw W b)
          atTop (𝓝 (-(4 * Real.pi * Parameters.semicircleDensity E) * v)) := by
    intro p' hc' h1 Q' hQ'
    let _i₀ : MeasurableSpace Ω₀ := m₀
    obtain ⟨-, hlim₀⟩ := nearPort_tendsto_pos hUnifLaw hUnifMom hBdry hInvU hb0 hb1 hE1 hE2 hx
      hy0 hy1 hxy hτ hj hc' one_pos h1 hQ' he hR₀
    refine ⟨_, fun Ω m 𝓖 P N X Y hR => ?_, hlim₀⟩
    let _i : MeasurableSpace Ω := m
    obtain ⟨hi, hlim⟩ := nearPort_tendsto_pos hUnifLaw hUnifMom hBdry hInvU hb0 hb1 hE1 hE2 hx
      hy0 hy1 hxy hτ hj hc' one_pos h1 hQ' he hR
    exact ⟨hi, mul_left_cancel₀ (absorptionConst_ne_zero hE1 hE2) (tendsto_nhds_unique hlim hlim₀)⟩
  obtain ⟨v₁, hv₁, hl₁⟩ := pos (fun t => p t + 1) (hpc.add continuous_const)
    (fun t => by linarith [hp0 t]) (Q + 1) (fun t => by linarith [hpQ t])
  obtain ⟨v₂, hv₂, hl₂⟩ := pos (fun _ => 1) continuous_const (fun _ => le_rfl) 1 (fun _ => le_rfl)
  refine ⟨v₁ - v₂, ResponseData.sub hτ.le (g₁ := fun s => p (τ - s)) (g₂ := fun _ => 1)
    (hpc.comp (continuous_const.sub continuous_id)) continuous_const hv₁ hv₂, ?_⟩
  have hlim := hl₁.sub hl₂
  rw [show -(4 * Real.pi * Parameters.semicircleDensity E) * v₁ -
      -(4 * Real.pi * Parameters.semicircleDensity E) * v₂ =
      -(4 * Real.pi * Parameters.semicircleDensity E) * (v₁ - v₂) by ring] at hlim
  refine hlim.congr' ?_
  obtain ⟨C, W₀, -, hC⟩ := portPass_uniform hUnifMom hInvU hb0 hb1 hE1 hE2 hx hy0 hy1 hτ hj
    hp0 hpQ he 0
  obtain ⟨C', W₀', -, hC'⟩ := portPass_uniform hUnifMom hInvU hb0 hb1 hE1 hE2 hx hy0 hy1 hτ hj
    (p := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl) he 0
  filter_upwards [eventually_ge_atTop (max W₀ W₀')] with W hW
  have i1 := (hC W (le_trans (le_max_left _ _) hW)).2.2.1
  have i2 := (hC' W (le_trans (le_max_right _ _) hW)).2.2.1
  have hpt : ∀ ω, portDeriv b (e W) x y W (j W) (fun t => p t + 1) 0 ω =
      portDeriv b (e W) x y W (j W) p 0 ω + portDeriv b (e W) x y W (j W) (fun _ => 1) 0 ω :=
    fun ω => portDeriv_add hp0 (fun _ => zero_le_one) 0 ω
  simp only [hpt]
  rw [integral_add i1 i2]
  ring

/-!
### Small profiles
-/

/-- For a profile `0 ≤ r ≤ ε'`: `D_i(r)` is integrable and `|E D_i(r)| ≤ 2c₁ε'(1 + (Cτ')²)`. -/
theorem abs_integral_portDeriv_small {b E x y : ℝ} {W n : ℕ} (hb0 : 0 ≤ b) (hb : b ≤ 1)
    (hE1 : -2 < E) (hE2 : E < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (hW : (1 : ℝ) ≤ W)
    {r : ℝ → ℝ} (hr0 : ∀ t, 0 ≤ r t) {ε' : ℝ} (hε' : 0 < ε') (hr : ∀ t, r t ≤ ε') {C τ' : ℝ}
    (hC : 0 ≤ C) (hn : ((n : ℝ) + 1) / W ≤ τ')
    (hclock : eLpNorm (fun ω => (W : ℂ)⁻¹ *
        ((boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω).trace)
        (ENNReal.ofReal 2) (growthPathLaw W b) ≤ ENNReal.ofReal (C * ((n : ℝ) + 1)))
    (i : Fin 2) :
    Integrable (fun ω => portDeriv b E x y W n r i ω) (growthPathLaw W b) ∧
      |∫ ω, portDeriv b E x y W n r i ω ∂growthPathLaw W b| ≤
        2 * ratioC1 x y * ε' * (1 + (C * τ') ^ 2) := by
  have : IsProbabilityMeasure (growthPathLaw W b) :=
    passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hF2 := trB_sq_moment hW hr0 hr hC hn hclock
  set TrB : GrowthPath W → ℝ := fun ω => (pencilSourceGram (fullPathMatrix b E W n ω)
    (sourceRoot W n r) (leadInclusion W n)).trace.re
  set M := (C * τ') ^ 2
  have hc₁ := ratioC1_nonneg hx hy0 hy1
  have hTrB0 : ∀ ω, 0 ≤ TrB ω := fun ω => by
    simp only [TrB, pencilSourceGram]
    rw [trace_conjTranspose_mul_self_re_eq_hsSq]; exact hsSq_nonneg _
  have hη0 := etaZ_nonneg hb hE1 hE2
  have hη1 := etaZ_le_one hb0 hE1 hE2
  set G : GrowthPath W → ℝ := fun ω => 2 * ratioC1 x y * (ε' + TrB ω ^ 2 / ε')
  have hGi : Integrable G (growthPathLaw W b) :=
    ((integrable_const ε').add (hF2.1.div_const ε')).const_mul _
  have hpt : ∀ᵐ ω ∂growthPathLaw W b, ‖portDeriv b E x y W n r i ω‖ ≤ G ω := by
    filter_upwards [ae_growthPath_isHermitian W b] with ω hω
    rw [Real.norm_eq_abs]
    refine (portDeriv_abs_le hb hE1 hE2 hx hy0 hy1 i hω).trans ?_
    have h1 : 2 * TrB ω ≤ ε' + TrB ω ^ 2 / ε' := by
      rw [← sub_nonneg]
      have : ε' + TrB ω ^ 2 / ε' - 2 * TrB ω = (ε' - TrB ω) ^ 2 / ε' := by field_simp; ring
      rw [this]; positivity
    have h2 : ratioC1 x y * (4 * etaZ b E * TrB ω) ≤ ratioC1 x y * (4 * TrB ω) := by
      have := hTrB0 ω
      have : 4 * etaZ b E * TrB ω ≤ 4 * TrB ω := by nlinarith
      exact mul_le_mul_of_nonneg_left this hc₁
    calc _ ≤ ratioC1 x y * (4 * TrB ω) := h2
      _ = 2 * ratioC1 x y * (2 * TrB ω) := by ring
      _ ≤ G ω := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hint : Integrable (fun ω => portDeriv b E x y W n r i ω) (growthPathLaw W b) :=
    Integrable.mono' hGi (measurable_portDeriv i).aestronglyMeasurable hpt
  refine ⟨hint, ?_⟩
  calc |∫ ω, portDeriv b E x y W n r i ω ∂growthPathLaw W b|
      ≤ ∫ ω, G ω ∂growthPathLaw W b := by
        refine (abs_integral_le_integral_abs).trans (integral_mono_ae hint.abs hGi ?_)
        filter_upwards [hpt] with ω h
        rwa [Real.norm_eq_abs] at h
    _ = 2 * ratioC1 x y * (ε' + (∫ ω, TrB ω ^ 2 ∂growthPathLaw W b) / ε') := by
        rw [integral_const_mul, integral_add (integrable_const ε') (hF2.1.div_const ε'),
          integral_div, integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ 2 * ratioC1 x y * (ε' + ε' ^ 2 * M / ε') := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (div_le_div_of_nonneg_right ?_ hε'.le)) (by positivity)
        have := hF2.2
        simpa [M, mul_pow] using this
    _ = 2 * ratioC1 x y * ε' * (1 + M) := by field_simp

/-!
### Far port
-/

theorem farPort_tendsto (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hInvU : PathFractionalInverseEnergyUniform) {b E x y τ Ce : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hxy : ¬(x = 0 ∧ y = 0)) (hτ : 0 < τ) {j : ℕ → ℕ}
    (hj : Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ)) {q : ℝ → ℝ} (hqc : Continuous q)
    (hq0 : ∀ t, 0 ≤ q t) {Q : ℝ} (hqQ : ∀ t, q t ≤ Q) {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) :
    ∃ v, ResponseData (transportD0 b E) τ q x y v ∧
      Tendsto (fun W : ℕ => ∫ ω, portDeriv b (e W) x y W (j W) q 1 ω ∂growthPathLaw W b) atTop
        (𝓝 (-(4 * Real.pi * Parameters.semicircleDensity E) * v)) := by
  set p : ℝ → ℝ := fun t => q (τ - t)
  have hpc : Continuous p := hqc.comp (continuous_const.sub continuous_id)
  obtain ⟨v, hv, hlim⟩ := nearPort_tendsto hUnifLaw hUnifMom hBdry hInvU hb0 hb1 hE1 hE2 hx hy0
    hy1 hxy hτ hj hpc (fun t => hq0 _) (fun t => hqQ _) he
  have hv' : ResponseData (transportD0 b E) τ q x y v :=
    hv.congr (funext fun s => by simp only [p, sub_sub_cancel])
  refine ⟨v, hv', ?_⟩
  set d₁ : ℕ → ℝ := fun W => ∫ ω, portDeriv b (e W) x y W (j W) q 1 ω ∂growthPathLaw W b
  set d₀ : ℕ → ℝ := fun W => ∫ ω, portDeriv b (e W) x y W (j W) p 0 ω ∂growthPathLaw W b
  suffices hdiff : Tendsto (fun W => d₁ W - d₀ W) atTop (𝓝 0) by
    have := hlim.add hdiff
    rw [add_zero] at this
    exact this.congr fun W => by simp only [d₁, d₀]; ring
  have hQ0 : 0 ≤ Q := (hq0 0).trans (hqQ 0)
  have hb1' : b ≤ 1 := by linarith
  obtain ⟨hκI, hEI⟩ := bulk_margin hE1 hE2
  obtain ⟨C₁, W₁, hC₁⟩ := hUnifMom.clock b hb0 hb1 _ Ce (τ + 1) 2 hκI one_le_two
  set C₁' := max C₁ 0
  set M := (C₁' * (τ + 2)) ^ 2
  have hc₁ := ratioC1_nonneg hx hy0 hy1
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (4 * ratioC1 x y * (1 + M) + 1)
  have hden : 0 < 4 * ratioC1 x y * (1 + M) + 1 := by positivity
  have hε' : 0 < ε' := div_pos hε hden
  have hsmall : 4 * ratioC1 x y * ε' * (1 + M) < ε := by
    have : 4 * ratioC1 x y * ε' * (1 + M) = ε * (4 * ratioC1 x y * (1 + M)) /
        (4 * ratioC1 x y * (1 + M) + 1) := by simp only [ε']; ring
    rw [this, div_lt_iff₀ hden]
    nlinarith
  -- uniform continuity of `q` on `[-1, τ + 2]`
  obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (-1 : ℝ)) (b := τ + 2)).uniformContinuousOn_of_continuous
      hqc.continuousOn) ε' hε'
  have hjn : Tendsto (fun W : ℕ => ((j W : ℝ) + 1) / W) atTop (𝓝 τ) := by
    have h1 : Tendsto (fun W : ℕ => (1 : ℝ) / W) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have := hj.add h1
    rw [add_zero] at this
    refine this.congr' (eventually_gt_atTop 0 |>.mono fun W hW => ?_)
    simp only
    rw [add_div]
  have hev : ∀ᶠ W : ℕ in atTop, W₁ ≤ W ∧ 1 ≤ W ∧ (j W : ℝ) / W < τ + 1 ∧
      |((j W : ℝ) + 1) / W - τ| < δ ∧ (-2 < e W ∧ e W < 2) := by
    refine (eventually_ge_atTop W₁).and ((eventually_ge_atTop 1).and
      ((hj.eventually (gt_mem_nhds (by linarith))).and
        (((Metric.tendsto_nhds.1 hjn δ hδ).mono fun W hW => by rwa [Real.dist_eq] at hW).and
          (IsMovingEnergy.eventually_bulk he hE1 hE2))))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 hev
  refine ⟨W₀, fun W hW => ?_⟩
  obtain ⟨hW1, hWge, hjW, hjδ, hbulk⟩ := hW₀ W hW
  rw [Real.dist_eq, sub_zero]
  have hWpos : 0 < W := by omega
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hWge
  have hW0 : (0 : ℝ) < W := by linarith
  set n := j W
  have hn : (n : ℝ) ≤ (τ + 1) * W := by rw [div_lt_iff₀ hW0] at hjW; linarith
  have hclock := (hC₁ W hW1 E hEI (e W) (he W hWpos) n hn).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by positivity)))
  have hnW : ((n : ℝ) + 1) / W ≤ τ + 2 := by rw [div_le_iff₀ hW0]; nlinarith
  -- the reversed grid profile and its comparison with `p`
  set q' : ℝ → ℝ := fun t => q (((n : ℝ) + 1) / W - t)
  have hgrid_rev : ∀ i : Fin n, q' (((n - i.val : ℕ) : ℝ) / W) =
      q (((n - (Fin.rev i).val : ℕ) : ℝ) / W) := by
    intro i
    have hi := i.isLt
    have h1 : (n - (Fin.rev i).val : ℕ) = i.val + 1 := by rw [val_rev']; omega
    simp only [q']
    congr 1
    rw [h1, Nat.cast_sub hi.le]
    push_cast
    field_simp
    ring
  set m : ℝ → ℝ := fun t => min (q' t) (p t)
  set r₁ : ℝ → ℝ := fun t => min (q' t - m t) ε'
  set r₂ : ℝ → ℝ := fun t => min (p t - m t) ε'
  have hclose : ∀ i : Fin n, |q' (((n - i.val : ℕ) : ℝ) / W) - p (((n - i.val : ℕ) : ℝ) / W)| <
      ε' := by
    intro i
    have hi := i.isLt
    set t := (((n - i.val : ℕ) : ℝ) / W)
    have ht : t = ((n : ℝ) - i.val) / W := by simp only [t]; rw [Nat.cast_sub hi.le]
    have ht0 : 0 ≤ t := by positivity
    have htn : t ≤ (n : ℝ) / W := by
      rw [ht]; exact div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) i.val]) hW0.le
    have hnW' : (n : ℝ) / W ≤ τ + 1 := hjW.le
    have ha : ((n : ℝ) + 1) / W - t ∈ Icc (-1 : ℝ) (τ + 2) := by
      constructor
      · have : ((n : ℝ) + 1) / W - t ≥ 0 := by
          rw [ht, ← sub_div]
          exact div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) i.val]) hW0.le
        linarith
      · have : ((n : ℝ) + 1) / W ≤ τ + 2 := hnW
        linarith
    have hb' : τ - t ∈ Icc (-1 : ℝ) (τ + 2) := ⟨by linarith, by linarith⟩
    have hd : dist (((n : ℝ) + 1) / W - t) (τ - t) < δ := by
      rw [Real.dist_eq, show ((n : ℝ) + 1) / W - t - (τ - t) = ((n : ℝ) + 1) / W - τ by ring]
      exact hjδ
    have := hUC _ ha _ hb' hd
    rwa [Real.dist_eq] at this
  have hgrid₁ : ∀ i : Fin n, (fun t => q' t - m t) (((n - i.val : ℕ) : ℝ) / W) =
      r₁ (((n - i.val : ℕ) : ℝ) / W) := by
    intro i
    have h := hclose i
    simp only [r₁, m]
    refine (min_eq_left ?_).symm
    rw [abs_lt] at h
    rcases le_total (q' (((n - i.val : ℕ) : ℝ) / W)) (p (((n - i.val : ℕ) : ℝ) / W)) with h' | h'
    · rw [min_eq_left h']; linarith
    · rw [min_eq_right h']; linarith
  have hgrid₂ : ∀ i : Fin n, (fun t => p t - m t) (((n - i.val : ℕ) : ℝ) / W) =
      r₂ (((n - i.val : ℕ) : ℝ) / W) := by
    intro i
    have h := hclose i
    simp only [r₂, m]
    refine (min_eq_left ?_).symm
    rw [abs_lt] at h
    rcases le_total (q' (((n - i.val : ℕ) : ℝ) / W)) (p (((n - i.val : ℕ) : ℝ) / W)) with h' | h'
    · rw [min_eq_left h']; linarith
    · rw [min_eq_right h']; linarith
  have hq'0 : ∀ t, 0 ≤ q' t := fun t => hq0 _
  have hp0' : ∀ t, 0 ≤ p t := fun t => hq0 _
  have hm0 : ∀ t, 0 ≤ m t := fun t => le_min (hq'0 t) (hp0' t)
  have hd1 : ∀ t, 0 ≤ q' t - m t := fun t => sub_nonneg.2 (min_le_left _ _)
  have hd2 : ∀ t, 0 ≤ p t - m t := fun t => sub_nonneg.2 (min_le_right _ _)
  have hr₁0 : ∀ t, 0 ≤ r₁ t := fun t => le_min (hd1 t) hε'.le
  have hr₂0 : ∀ t, 0 ≤ r₂ t := fun t => le_min (hd2 t) hε'.le
  -- pointwise decompositions
  have hdec₁ : ∀ ω, portDeriv b (e W) x y W n q' 0 ω =
      portDeriv b (e W) x y W n m 0 ω + portDeriv b (e W) x y W n r₁ 0 ω := by
    intro ω
    have h := portDeriv_add (b := b) (E := e W) (x := x) (y := y) (W := W) (n := n) hm0 hd1 0 ω
    have e1 : (fun t => m t + (q' t - m t)) = q' := funext fun t => by ring
    rw [e1] at h
    rw [h, portDeriv_congr_grid (q := fun t => q' t - m t) (r := r₁) hgrid₁]
  have hdec₂ : ∀ ω, portDeriv b (e W) x y W n p 0 ω =
      portDeriv b (e W) x y W n m 0 ω + portDeriv b (e W) x y W n r₂ 0 ω := by
    intro ω
    have h := portDeriv_add (b := b) (E := e W) (x := x) (y := y) (W := W) (n := n) hm0 hd2 0 ω
    have e1 : (fun t => m t + (p t - m t)) = p := funext fun t => by ring
    rw [e1] at h
    rw [h, portDeriv_congr_grid (q := fun t => p t - m t) (r := r₂) hgrid₂]
  -- integrability and bounds
  have hmQ : ∀ t, m t ≤ Q + 1 := fun t => (min_le_right _ _).trans (by linarith [hqQ (τ - t)])
  obtain ⟨im, -⟩ := abs_integral_portDeriv_small (x := x) (y := y) (i := 0) hb0.le hb1' hbulk.1
    hbulk.2 hx hy0 hy1 hWr hm0 (by linarith : (0 : ℝ) < Q + 1) hmQ (le_max_right C₁ 0) hnW hclock
  obtain ⟨i₁, b₁⟩ := abs_integral_portDeriv_small (x := x) (y := y) (i := 0) hb0.le hb1' hbulk.1
    hbulk.2 hx hy0 hy1 hWr hr₁0 hε' (fun t => min_le_right _ _) (le_max_right C₁ 0) hnW hclock
  obtain ⟨i₂, b₂⟩ := abs_integral_portDeriv_small (x := x) (y := y) (i := 0) hb0.le hb1' hbulk.1
    hbulk.2 hx hy0 hy1 hWr hr₂0 hε' (fun t => min_le_right _ _) (le_max_right C₁ 0) hnW hclock
  -- the far port through the reversal
  have hrev : d₁ W = ∫ ω, portDeriv b (e W) x y W n q' 0 ω ∂growthPathLaw W b := by
    simp only [d₁]
    rw [← integral_revPath W b n (measurable_portDeriv 0)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact (portDeriv_one_revPath hgrid_rev ω).symm
  have hval : d₁ W - d₀ W = (∫ ω, portDeriv b (e W) x y W n r₁ 0 ω ∂growthPathLaw W b) -
      ∫ ω, portDeriv b (e W) x y W n r₂ 0 ω ∂growthPathLaw W b := by
    have hd0 : d₀ W = ∫ ω, portDeriv b (e W) x y W n p 0 ω ∂growthPathLaw W b := rfl
    rw [hrev, hd0]
    simp only [hdec₁, hdec₂]
    rw [integral_add im i₁, integral_add im i₂]
    ring
  rw [hval]
  calc |(∫ ω, portDeriv b (e W) x y W n r₁ 0 ω ∂growthPathLaw W b) -
        ∫ ω, portDeriv b (e W) x y W n r₂ 0 ω ∂growthPathLaw W b|
      ≤ |∫ ω, portDeriv b (e W) x y W n r₁ 0 ω ∂growthPathLaw W b| +
        |∫ ω, portDeriv b (e W) x y W n r₂ 0 ω ∂growthPathLaw W b| := abs_sub _ _
    _ ≤ 2 * ratioC1 x y * ε' * (1 + M) + 2 * ratioC1 x y * ε' * (1 + M) := add_le_add b₁ b₂
    _ = 4 * ratioC1 x y * ε' * (1 + M) := by ring
    _ < ε := hsmall

end BlockBand.Endpoints
