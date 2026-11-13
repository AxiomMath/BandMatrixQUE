module

public import BlockBand.Endpoints.Poisson.SingleCollarAssemblySteps

/-!
# The single-collar log-error bound from its inputs

Law: the original prior `ringCoordLaw` of each `s.parameters b j`.

* `scStageLogErrorPointwise_of_parts`: `ScStageLogErrorPointwise` from `CollarKernelContract`,
  `MatchedTracesContract` and `TransmissionLengthUniformContract`, and the three hypotheses
  `RemoteHigherUniformStatement`, `ScsWardScattering` and `ScsStageLogMoment`.
* `svSingleCollarLogError_of_parts`, `peSameVolumeLogError_of_parts`: the composites with
  `svSingleCollarLogError_of_pointwise'` and `peSameVolumeLogError_of_singleCollar`.

Proof. `p = 1/8`; four instances `(p', r) ∈ {1/8, 1/16} × {1, 2}` of
`RemoteHigherUniformStatement` with window constant `K = 2X/ρ + 1`; `c = c₀/2`, `c₀` the least
rate. After `δ`: `ScsStageLogMoment` at `K = δ/ρ` (`κn/W = δ/ρ`), `scs_stage_bound` at
`κI = (2 - |E|)/2`, the defect moment at `ε = 1`; `κ ≤ 2δ/ρ`, `Im z_b ≤ 1`.
* `R < 4`: `E|ΔB| ≤ ‖ΔB‖_{L^r} ≤ M ≤ M e^{4c} m² e^{-cR}`.
* `R ≥ 4`, by contradiction: a bad energy `x_l` is chosen at each index of a bad
  subsequence, then the Ward data at that energy, then Bolzano–Weierstrass on the component
  lengths. Along the sub-subsequence the profiles `1_{[R-1, τ_i-(R-1)]}` are `1` on the source
  windows eventually, the remote-higher moments are eventually `≤ Cs e^{-c₀(R-1)} + ε''`
  (`sca2_component_eventually`), so `E(σ̄ + σ̄²) ≤ A` (`sca2_sigma_moment`), and
  `scs_stage_bound` with the certificate at `D = 1`, `T = τ + 1` gives the bound, a
  contradiction.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace intervalSource growthPathLaw)
open BlockBand.Internal.Contracts.Layers (boundaryZ bulkInterval MatchedTracesContract)
open BlockBand.Internal.Contracts.Critical (CollarKernelContract conductance oldScattering)
open BlockBand.Internal.Contracts.TransmissionUniform (TransmissionLengthUniformContract)
open scoped ENNReal

/-- **The single-collar log error (pointwise form) from its parts.** Hypotheses: `CollarKernelContract`,
`MatchedTracesContract`, `TransmissionLengthUniformContract`, `RemoteHigherUniformStatement`, `ScsWardScattering`
(proved as `scsWardScattering`) and `ScsStageLogMoment` (proved from `PassiveLog` as
`scsStageLogMoment_of_passiveLog`). -/
theorem scStageLogErrorPointwise_of_parts (hK : CollarKernelContract)
    (hMT : MatchedTracesContract) (hTU : TransmissionLengthUniformContract)
    (hRHU : RemoteHigherUniformStatement) (hWard : ScsWardScattering)
    (hMom : ScsStageLogMoment) : ScStageLogErrorPointwise := by
  intro b hb hb' E hE1 hE2 X hX
  set ρ := Parameters.semicircleDensity E with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]; unfold Parameters.semicircleDensity
    have : 0 < 4 - E ^ 2 := by nlinarith
    exact div_pos (Real.sqrt_pos.2 this) (by positivity)
  set κI : ℝ := (2 - |E|) / 2 with hκIdef
  have hEabs : |E| < 2 := abs_lt.2 ⟨hE1, hE2⟩
  have hκI : 0 < κI := by rw [hκIdef]; linarith
  set KR : ℝ := 2 * X / ρ + 1 with hKR
  have hKR0 : 0 ≤ KR := by positivity
  obtain ⟨C11, c11, hc11, hU11⟩ := hRHU b hb hb' E hE1 hE2 (1 / 8) 1 (by norm_num) (by norm_num)
    le_rfl (by norm_num) KR hKR0
  obtain ⟨C12, c12, hc12, hU12⟩ := hRHU b hb hb' E hE1 hE2 (1 / 8) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) KR hKR0
  obtain ⟨C21, c21, hc21, hU21⟩ := hRHU b hb hb' E hE1 hE2 (1 / 8 / 2) 1 (by norm_num)
    (by norm_num) le_rfl (by norm_num) KR hKR0
  obtain ⟨C22, c22, hc22, hU22⟩ := hRHU b hb hb' E hE1 hE2 (1 / 8 / 2) 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) KR hKR0
  set c₀ : ℝ := min (min c11 c12) (min c21 c22) with hc₀def
  have hc₀ : 0 < c₀ := lt_min (lt_min hc11 hc12) (lt_min hc21 hc22)
  set Cs : ℝ := max (max (max C11 C12) (max C21 C22)) 0 with hCsdef
  have hCs : 0 ≤ Cs := le_max_right _ _
  refine ⟨c₀ / 2, by positivity, fun δ hδ => ?_⟩
  obtain ⟨r, M, hr, hMr⟩ := hMom b hb hb' (δ / ρ) (by positivity)
  obtain ⟨d₂, cstar, W₀, hd₂, hcstar, hSB⟩ := scs_stage_bound hK hb hb' hκI
  obtain ⟨Cp, hCp, hSBp⟩ := hSB (1 / 8) (by norm_num) (by norm_num)
  obtain ⟨Cg0, hCg0⟩ := sequentialCollars_conductance hTU hb hb' hκI one_pos
  set Cg : ℝ := max Cg0 0 with hCgdef
  set M' : ℝ := max M 0 with hM'def
  have hM' : 0 ≤ M' := le_max_right _ _
  set κm : ℝ := 2 * δ / ρ with hκmdef
  have hκm : 0 ≤ κm := by positivity
  set K₂ : ℝ := sca2K2 (1 / 8) 1 κm with hK₂def
  have hK₂ : 0 ≤ K₂ := sca2K2_nonneg zero_le_one hκm
  set C₁ : ℝ := (Cp * K₂ * Cs + Cp * (Real.sqrt Cg * Real.sqrt (K₂ * Cs))) *
    Real.exp (c₀ / 2) with hC₁def
  set C₂ : ℝ := M' * Real.exp (4 * (c₀ / 2)) with hC₂def
  have hC₂ : 0 ≤ C₂ := by positivity
  refine ⟨max C₁ C₂, le_max_of_le_right hC₂, ?_⟩
  intro m a R τ hR hτ ha hgap s nb hnb hlim hsum π S k hk ε hε
  have hm : 1 ≤ m := Fin.pos k
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- common facts along the critical sequence
  have hΛ := sc_tendsto_lambda s hb hb' hρ
  have hWt : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  have hNeq : ∀ j, ((s.parameters b hb hb' j).N : ℝ) = (s.n j : ℝ) * (s.W j : ℝ) := fun j => by
    simp [CriticalSequence.parameters, Parameters.N]
  have hn0 : ∀ j, (0 : ℝ) < s.n j := fun j =>
    Nat.cast_pos.2 (lt_of_lt_of_le (by norm_num) (s.n_ge_four j))
  have hW0 : ∀ j, (0 : ℝ) < s.W j := fun j => Nat.cast_pos.2 (s.W_pos j)
  have hbulk : ∀ᶠ j in atTop, ∀ x ∈ Icc (-X) X,
      E + x / (((s.parameters b hb hb' j).N : ℝ) * ρ) ∈ bulkInterval κI := by
    have ht : Tendsto (fun j => X / (((s.parameters b hb hb' j).N : ℝ) * ρ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hΛ
    filter_upwards [ht.eventually (gt_mem_nhds hκI), hΛ.eventually_gt_atTop 0] with j hj hj' x hx
    have hxl : |x / (((s.parameters b hb hb' j).N : ℝ) * ρ)| ≤
        X / (((s.parameters b hb hb' j).N : ℝ) * ρ) := by
      rw [abs_div, abs_of_pos hj']
      exact div_le_div_of_nonneg_right (abs_le.2 ⟨hx.1, hx.2⟩) hj'.le
    have h3 := abs_le.1 (hxl.trans hj.le)
    have hEa := neg_abs_le E
    have hEb := le_abs_self E
    simp only [bulkInterval, mem_Icc]
    constructor <;> linarith only [h3.1, h3.2, hEa, hEb, hκIdef]
  -- the energy, source and layout facts at one index
  have hfacts : ∀ j, (∑ i, nb j i = s.n j) → ∀ x ∈ Icc (-X) X,
      E + x / (((s.parameters b hb hb' j).N : ℝ) * ρ) ∈ bulkInterval κI →
      IsCollarLayout (s.parameters b hb hb' j).n (svLayout (nb j)) ∧
      -2 < E + x / (((s.parameters b hb hb' j).N : ℝ) * ρ) ∧
      E + x / (((s.parameters b hb hb' j).N : ℝ) * ρ) < 2 ∧
      0 ≤ δ * ((s.parameters b hb hb' j).W : ℝ) ^ 2 / (((s.parameters b hb hb' j).N : ℝ) * ρ) ∧
      δ * ((s.parameters b hb hb' j).W : ℝ) ^ 2 / (((s.parameters b hb hb' j).N : ℝ) * ρ) *
        (s.parameters b hb hb' j).n / (s.parameters b hb hb' j).W ≤ δ / ρ := by
    intro j hsj x hx he
    refine ⟨sv_isCollarLayout (hnb j) hsj, by linarith only [he.1, hκI], by linarith only [he.2, hκI], by positivity,
      le_of_eq ?_⟩
    have := hn0 j; have := hW0 j
    change δ * (s.W j : ℝ) ^ 2 / (((s.parameters b hb hb' j).N : ℝ) * ρ) * (s.n j) / (s.W j) = _
    rw [hNeq]
    field_simp
  rcases lt_or_ge R 4 with hR4 | hR4
  · ---------------- `R < 4`: the moment bound
    filter_upwards [hsum, hbulk] with j hsj hbj x hx
    obtain ⟨hL, he1, he2, hκ0, hκK⟩ := hfacts j hsj x hx (hbj x hx)
    have key := hMr (s.parameters b hb hb' j) rfl (svLayout (nb j)) hL π S k hk
      ⌊R * (s.W j : ℝ)⌋₊ _ he1 he2 _ hκ0 hκK
    have hle := sca2_lintegral_le_eLpNorm (μ := ringCoordLaw (s.parameters b hb hb' j).n
      (s.parameters b hb hb' j).W (s.parameters b hb hb' j).b)
      (sca2_measurable_stageLogDiff (s.parameters b hb hb' j) (svLayout (nb j)) π S k
        (E + x / (((s.parameters b hb hb' j).N : ℝ) * ρ)) ⌊R * (s.W j : ℝ)⌋₊
        (δ * ((s.parameters b hb hb' j).W : ℝ) ^ 2 / (((s.parameters b hb hb' j).N : ℝ) * ρ)))
      hr.le
    refine (le_of_eq_of_le rfl (hle.trans key)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 1 ≤ Real.exp (4 * (c₀ / 2)) * Real.exp (-(c₀ / 2 * R)) := by
      rw [← Real.exp_add]
      have := mul_nonneg (half_pos hc₀).le (sub_nonneg.2 hR4.le)
      exact Real.one_le_exp (by linarith only [this])
    have h2 : M' ≤ C₂ * (m : ℝ) ^ 2 * Real.exp (-(c₀ / 2 * R)) := by
      have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hm'
      calc M' = M' * 1 * 1 := by ring
        _ ≤ M' * (m : ℝ) ^ 2 * (Real.exp (4 * (c₀ / 2)) * Real.exp (-(c₀ / 2 * R))) := by
          gcongr
        _ = C₂ * (m : ℝ) ^ 2 * Real.exp (-(c₀ / 2 * R)) := by rw [hC₂def]; ring
    have h3 : C₂ * (m : ℝ) ^ 2 * Real.exp (-(c₀ / 2 * R)) ≤
        max C₁ C₂ * (m : ℝ) ^ 2 * Real.exp (-(c₀ / 2 * R)) := by
      gcongr; exact le_max_right _ _
    linarith only [le_max_left M 0, hM'def, h2, h3, hε]
  · ---------------- `R ≥ 4`
    set B₀ : ℝ := Cs * Real.exp (-(c₀ * (R - 1))) with hB₀
    have hB₀0 : 0 ≤ B₀ := by positivity
    obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun A => Cp * (A + Real.sqrt Cg * Real.sqrt A) := ⟨_, rfl⟩
    have hFc : Continuous F := by
      rw [hF]
      exact continuous_const.mul (continuous_id.add
        (continuous_const.mul Real.continuous_sqrt))
    have hT : Tendsto (fun t => F (K₂ * (m : ℝ) ^ 2 * (B₀ + t))) (𝓝[>] 0)
        (𝓝 (F (K₂ * (m : ℝ) ^ 2 * B₀))) := by
      have hc : Continuous (fun t => F (K₂ * (m : ℝ) ^ 2 * (B₀ + t))) :=
        hFc.comp (continuous_const.mul (continuous_const.add continuous_id))
      have h := hc.tendsto 0
      simp only [add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    obtain ⟨ε'', hε''F, hε''0⟩ := ((hT.eventually (gt_mem_nhds
      (lt_add_of_pos_right (F (K₂ * (m : ℝ) ^ 2 * B₀)) (half_pos hε)))).and
      self_mem_nhdsWithin).exists
    have hε''pos : 0 < ε'' := hε''0
    set A : ℝ := K₂ * (m : ℝ) ^ 2 * (B₀ + ε'') with hAdef
    have hA0 : 0 ≤ A := by positivity
    have hs1 : 0 < 1 - 1 / r := by
      have : 1 / r < 1 := (div_lt_one (by linarith only [hr])).2 hr
      linarith only [this]
    obtain ⟨Wc, hWc⟩ := sequentialCollars_certificate hMT hb hb' hκI hd₂ 1 (τ + 1)
    obtain ⟨Wg, hWg⟩ := hCg0 (τ + 1)
    have hsmall : ∀ᶠ j in atTop, M' * (((s.parameters b hb hb' j).W : ℝ) ^ (-((1 : ℕ) : ℝ)) +
        A / (cstar * ((s.parameters b hb hb' j).W : ℝ))) ^ (1 - 1 / r) < ε / 2 := by
      have t1 : Tendsto (fun j => (s.W j : ℝ) ^ (-((1 : ℕ) : ℝ))) atTop (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop one_pos).comp hWt
        simpa [Function.comp_def] using this
      have t2 : Tendsto (fun j => A / (cstar * (s.W j : ℝ))) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (hWt.const_mul_atTop hcstar)
      have t3 := t1.add t2
      rw [add_zero] at t3
      have t4 := ((Real.continuousAt_rpow_const 0 (1 - 1 / r) (Or.inr hs1.le)).tendsto).comp t3
      rw [Real.zero_rpow hs1.ne'] at t4
      have t5 := t4.const_mul M'
      rw [mul_zero] at t5
      exact t5.eventually (gt_mem_nhds (half_pos hε))
    have hnb3 : ∀ᶠ j in atTop, ∀ i, s.W j + 3 ≤ nb j i := by
      rw [eventually_all]
      intro i
      have h2i : (2 : ℝ) < a i * τ := by linarith only [hgap i, hR]
      filter_upwards [(hlim i).eventually (lt_mem_nhds h2i), s.width_tendsto.eventually_ge_atTop 3]
        with j hj hW3
      have hWj := hW0 j
      have h1 : 2 * (s.W j : ℝ) < nb j i := by rwa [lt_div_iff₀ hWj] at hj
      have h3 : (3 : ℝ) ≤ s.W j := by exact_mod_cast hW3
      have : (s.W j : ℝ) + 3 < nb j i := by linarith only [h1, h3]
      exact_mod_cast this.le
    have hgood : ∀ᶠ j in atTop,
        (∑ i, nb j i = s.n j) ∧
        (∀ x ∈ Icc (-X) X, E + x / (((s.parameters b hb hb' j).N : ℝ) * ρ) ∈ bulkInterval κI) ∧
        max (max W₀ Wc) (max Wg 3) ≤ s.W j ∧
        (s.n j : ℝ) ≤ (τ + 1) * s.W j ∧ (s.W j : ℝ) ≤ 2 * s.n j ∧
        (∀ i, s.W j + 3 ≤ nb j i) ∧
        M' * (((s.parameters b hb hb' j).W : ℝ) ^ (-((1 : ℕ) : ℝ)) +
          A / (cstar * ((s.parameters b hb hb' j).W : ℝ))) ^ (1 - 1 / r) < ε / 2 := by
      filter_upwards [hsum, hbulk, s.width_tendsto.eventually_ge_atTop (max (max W₀ Wc) (max Wg 3)),
        s.ratio_tendsto.eventually (gt_mem_nhds (lt_add_one τ)),
        s.ratio_tendsto.eventually (lt_mem_nhds (by linarith only [hτ] : (1 : ℝ) / 2 < τ)), hnb3, hsmall]
        with j h1 h2 h3 h4 h5 h6 h7
      have hWj := hW0 j
      refine ⟨h1, h2, h3, ?_, ?_, h6, h7⟩
      · rw [div_lt_iff₀ hWj] at h4; exact h4.le
      · rw [lt_div_iff₀ hWj] at h5; linarith only [h5]
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop (hcon.and_eventually hgood)
    have hx := fun l => (hφP l).1
    push Not at hx
    choose x hxI hxbad using hx
    have hgφ := fun l => (hφP l).2
    -- the Ward data at the chosen bad energy
    have hD : ∀ l, Nonempty (ScsWardData (s.parameters b hb hb' (φ l)) (svLayout (nb (φ l))) 0 π
        S k (E + x l / (((s.parameters b hb hb' (φ l)).N : ℝ) * ρ)) ⌊R * (s.W (φ l) : ℝ)⌋₊
        (δ * ((s.parameters b hb hb' (φ l)).W : ℝ) ^ 2 /
          (((s.parameters b hb hb' (φ l)).N : ℝ) * ρ))) := by
      intro l
      obtain ⟨h1, h2, -⟩ := hgφ l
      obtain ⟨hL, he1, he2, hκ0, -⟩ := hfacts (φ l) h1 (x l) (hxI l) (h2 (x l) (hxI l))
      exact hWard _ _ hL π S k hk _ _ he1 he2 _ hκ0
    set D := fun l => Classical.choice (hD l) with hDdef
    clear_value D
    clear hDdef
    -- Bolzano–Weierstrass on the component lengths
    obtain ⟨Bn, hBn⟩ : ∃ Bn : ℝ, ∀ j, (s.n j : ℝ) / s.W j ≤ Bn := by
      obtain ⟨Bn, hBn⟩ := (Metric.isBounded_range_of_tendsto _ s.ratio_tendsto).bddAbove
      exact ⟨Bn, fun j => hBn (mem_range_self j)⟩
    have hvK : ∀ l, (fun i => ((D l).len i : ℝ) / (s.W (φ l) : ℝ)) ∈
        Set.univ.pi (fun _ : Fin m => Icc (0 : ℝ) Bn) := by
      intro l
      refine Set.mem_univ_pi.2 fun i => ⟨by positivity, ?_⟩
      refine le_trans ?_ (hBn (φ l))
      have : ((D l).len i : ℝ) ≤ (s.n (φ l) : ℝ) := Nat.cast_le.2 ((D l).len_le i)
      exact div_le_div_of_nonneg_right this (hW0 _).le
    obtain ⟨τv, hτvK, ψ, hψ, hconv⟩ :=
      (isCompact_univ_pi fun _ => isCompact_Icc).tendsto_subseq hvK
    have hτv0 : ∀ i, 0 ≤ τv i := fun i => (Set.mem_univ_pi.1 hτvK i).1
    have hconvi : ∀ i, Tendsto (fun l => ((D (ψ l)).len i : ℝ) / (s.W (φ (ψ l)) : ℝ)) atTop
        (𝓝 (τv i)) := fun i => tendsto_pi_nhds.1 hconv i
    have hjl : Tendsto (fun l => φ (ψ l)) atTop atTop := (hφ.comp hψ).tendsto_atTop
    have hWl : Tendsto (fun l => s.W (φ (ψ l))) atTop atTop := s.width_tendsto.comp hjl
    have hWlr : Tendsto (fun l => (s.W (φ (ψ l)) : ℝ)) atTop atTop := hWt.comp hjl
    -- the source windows
    have hwinev : ∀ᶠ l in atTop, ∀ i,
        ((D (ψ l)).len i : ℝ) / s.W (φ (ψ l)) + 3 / s.W (φ (ψ l)) ≤ τv i + 1 := by
      rw [eventually_all]
      intro i
      have h3 : Tendsto (fun l => (3 : ℝ) / s.W (φ (ψ l))) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hWlr
      have h := (hconvi i).add h3
      rw [add_zero] at h
      exact (h.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le
    -- the energies are in the remote-higher window
    have hel : ∀ᶠ l in atTop, |E + x (ψ l) / (((s.parameters b hb hb' (φ (ψ l))).N : ℝ) * ρ) - E|
        ≤ KR / ((s.W (φ (ψ l)) : ℕ) : ℝ) ^ 2 := by
      refine Eventually.of_forall fun l => ?_
      obtain ⟨-, -, -, -, h5, -, -⟩ := hgφ (ψ l)
      have hxa : |x (ψ l)| ≤ X := abs_le.2 ⟨(hxI (ψ l)).1, (hxI (ψ l)).2⟩
      rw [add_sub_cancel_left, hNeq]
      exact (sca2_scale (hn0 _) (hW0 _) hρ hδ hX hxa h5).1
    -- the four remote-higher moments of each component
    have hmono : ∀ C' c' : ℝ, C' ≤ Cs → c₀ ≤ c' →
        max C' 0 * Real.exp (-(c' * (R - 1))) + ε'' ≤ B₀ + ε'' := by
      intro C' c' h1 h2
      have he : Real.exp (-(c' * (R - 1))) ≤ Real.exp (-(c₀ * (R - 1))) := by
        rw [Real.exp_le_exp]
        have : c₀ * (R - 1) ≤ c' * (R - 1) := mul_le_mul_of_nonneg_right h2 (by linarith only [hR4])
        linarith only [this]
      have hmx : max C' 0 ≤ Cs := max_le h1 hCs
      have : max C' 0 * Real.exp (-(c' * (R - 1))) ≤ Cs * Real.exp (-(c₀ * (R - 1))) :=
        mul_le_mul hmx he (Real.exp_pos _).le hCs
      rw [hB₀]
      exact add_le_add_left this _
    have hC11 : C11 ≤ Cs := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
    have hC12 : C12 ≤ Cs := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
    have hC21 : C21 ≤ Cs := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
    have hC22 : C22 ≤ Cs := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
    have hc11' : c₀ ≤ c11 := (min_le_left _ _).trans (min_le_left _ _)
    have hc12' : c₀ ≤ c12 := (min_le_left _ _).trans (min_le_right _ _)
    have hc21' : c₀ ≤ c21 := (min_le_right _ _).trans (min_le_left _ _)
    have hc22' : c₀ ≤ c22 := (min_le_right _ _).trans (min_le_right _ _)
    have hR1 : (2 : ℝ) ≤ R - 1 := by linarith only [hR4]
    have hcomp : ∀ i, ∀ᶠ l in atTop, ∀ q ∈ ({1 / 8, 1 / 8 / 2} : Set ℝ),
        ∀ r' ∈ ({1, 2} : Set ℝ),
        ∫⁻ ω, ENNReal.ofReal (fracTrace q (intervalSource b
            (E + x (ψ l) / (((s.parameters b hb hb' (φ (ψ l))).N : ℝ) * ρ)) (s.W (φ (ψ l)))
            ((D (ψ l)).len i) ((Icc (R - 1) (τv i - (R - 1))).indicator 1) ω)) ^ r'
          ∂growthPathLaw (s.W (φ (ψ l))) b ≤ ENNReal.ofReal (B₀ + ε'') := by
      intro i
      have e11 := sca2_component_eventually (by norm_num) (by norm_num) hR1 (hτv0 i) hKR0 hU11 hWl
        (hconvi i) hel hε''pos
      have e12 := sca2_component_eventually (by norm_num) (by norm_num) hR1 (hτv0 i) hKR0 hU12 hWl
        (hconvi i) hel hε''pos
      have e21 := sca2_component_eventually (by norm_num) (by norm_num) hR1 (hτv0 i) hKR0 hU21 hWl
        (hconvi i) hel hε''pos
      have e22 := sca2_component_eventually (by norm_num) (by norm_num) hR1 (hτv0 i) hKR0 hU22 hWl
        (hconvi i) hel hε''pos
      filter_upwards [e11, e12, e21, e22] with l h11 h12 h21 h22
      intro q hq r' hr'
      rcases hq with rfl | rfl <;> rcases hr' with rfl | rfl
      · exact h11.trans (ENNReal.ofReal_le_ofReal (hmono _ _ hC11 hc11'))
      · exact h12.trans (ENNReal.ofReal_le_ofReal (hmono _ _ hC12 hc12'))
      · exact h21.trans (ENNReal.ofReal_le_ofReal (hmono _ _ hC21 hc21'))
      · exact h22.trans (ENNReal.ofReal_le_ofReal (hmono _ _ hC22 hc22'))
    -- one index of the sub-subsequence where everything holds
    obtain ⟨l, hwl, hcl⟩ := (hwinev.and (eventually_all.2 hcomp)).exists
    refine absurd ?_ (not_le.2 (hxbad (ψ l)))
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hgφ (ψ l)
    obtain ⟨hL, he1, he2, hκ0, hκK⟩ := hfacts (φ (ψ l)) h1 (x (ψ l)) (hxI (ψ l))
      (h2 (x (ψ l)) (hxI (ψ l)))
    have he := h2 (x (ψ l)) (hxI (ψ l))
    have hxa : |x (ψ l)| ≤ X := abs_le.2 ⟨(hxI (ψ l)).1, (hxI (ψ l)).2⟩
    obtain ⟨-, hκle, -⟩ := sca2_scale (hn0 (φ (ψ l))) (hW0 (φ (ψ l))) hρ hδ hX hxa h5
    have hκm' : δ * ((s.parameters b hb hb' (φ (ψ l))).W : ℝ) ^ 2 /
        (((s.parameters b hb hb' (φ (ψ l))).N : ℝ) * ρ) ≤ κm := by
      change δ * (s.W (φ (ψ l)) : ℝ) ^ 2 / (((s.parameters b hb hb' (φ (ψ l))).N : ℝ) * ρ) ≤ κm
      rw [hNeq]; exact hκle
    have hW3 : (3 : ℝ) ≤ s.W (φ (ψ l)) := by
      have : 3 ≤ s.W (φ (ψ l)) := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h3)
      exact_mod_cast this
    have hη0 := (boundaryZ_im_pos (b := b) (hb'.trans (by norm_num)) he1 he2).le
    have hη1 := sca2_boundaryZ_im_le_one hb he1 he2
    -- the four inputs of `scs_stage_bound`
    have hcond := hWg (s.parameters b hb hb' (φ (ψ l))) rfl
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h3)) h4 (svLayout (nb (φ (ψ l))))
      0 hL (fun i => by
        have h6i : (s.W (φ (ψ l)) : ℝ) + 3 ≤ nb (φ (ψ l)) i := by exact_mod_cast h6 i
        change (1 : ℝ) * (s.W (φ (ψ l)) : ℝ) ≤ ((nb (φ (ψ l)) i - 3 : ℕ) : ℝ)
        rw [Nat.cast_sub (le_trans (Nat.le_add_left 3 _) (h6 i)), one_mul]
        push_cast
        linarith only [h6i]) π S k hk ⌊R * (s.W (φ (ψ l)) : ℝ)⌋₊ _ he
    have hcond' := (lintegral_mono fun ω => sca2_cond_le b _ _).trans
      (hcond.trans (ENNReal.ofReal_le_ofReal (le_max_left Cg0 0)))
    have hsig := sca2_sigma_moment (s.parameters b hb hb' (φ (ψ l))) hm (svLayout (nb (φ (ψ l))))
      π S k _ _ _ (D (ψ l)) (p := 1 / 8) (ηm := 1) (κm := κm) (B := B₀ + ε'') (by norm_num)
      (by norm_num) hη0 hη1 hκ0 hκm' (fun i => (Icc (R - 1) (τv i - (R - 1))).indicator 1)
      (fun i y => by
        simp only [indicator_apply, Pi.one_apply]
        split_ifs <;> norm_num)
      (fun i y hy => by
        have hbuf : R * (s.W (φ (ψ l)) : ℝ) - 1 < (⌊R * (s.W (φ (ψ l)) : ℝ)⌋₊ : ℝ) := by
          have := Nat.lt_floor_add_one (R * (s.W (φ (ψ l)) : ℝ)); linarith only [this]
        have hy' := sca2_window hW3 hbuf (hwl i) hy
        exact indicator_of_mem hy' _)
      (fun i => hcl i)
    have hLr := (hMr (s.parameters b hb hb' (φ (ψ l))) rfl (svLayout (nb (φ (ψ l)))) hL π S k hk
      ⌊R * (s.W (φ (ψ l)) : ℝ)⌋₊ _ he1 he2 _ hκ0 hκK).trans (ENNReal.ofReal_le_ofReal
        (le_max_left M 0))
    have hWcle : Wc ≤ s.W (φ (ψ l)) := le_trans (le_max_right W₀ Wc) (le_trans (le_max_left _ _) h3)
    have hW₀le : W₀ ≤ s.W (φ (ψ l)) := le_trans (le_max_left W₀ Wc) (le_trans (le_max_left _ _) h3)
    have hcert := hWc (s.parameters b hb hb' (φ (ψ l))) rfl hWcle h4 (svLayout (nb (φ (ψ l))))
      0 hL π S k hk ⌊R * (s.W (φ (ψ l)) : ℝ)⌋₊ _ he
    have key := hSBp (s.parameters b hb hb' (φ (ψ l))) rfl hW₀le (svLayout (nb (φ (ψ l)))) hL
      π S k hk ⌊R * (s.W (φ (ψ l)) : ℝ)⌋₊ _ he _ hκ0 (D (ψ l)) (le_max_right Cg0 0) hA0
      (by positivity) hr hcond' hsig hLr hcert
    refine (le_of_eq_of_le rfl key).trans ?_
    -- the arithmetic
    have hFA : Cp * (A + Real.sqrt Cg * Real.sqrt A) < F (K₂ * (m : ℝ) ^ 2 * B₀) + ε / 2 := by
      have := hε''F; rw [hF] at this ⊢; exact this
    have hFB : F (K₂ * (m : ℝ) ^ 2 * B₀) ≤ C₁ * (m : ℝ) ^ 2 * Real.exp (-(c₀ / 2 * R)) := by
      rw [hF]; exact sca2_F_bound hCp hK₂ hCs hc₀ (by linarith only [hR4]) hm'
    have hC1 : C₁ * (m : ℝ) ^ 2 * Real.exp (-(c₀ / 2 * R)) ≤
        max C₁ C₂ * (m : ℝ) ^ 2 * Real.exp (-(c₀ / 2 * R)) := by
      gcongr; exact le_max_left _ _
    rw [← ENNReal.ofReal_add hA0 (by positivity), ← ENNReal.ofReal_mul hCp,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hs1.le, ← ENNReal.ofReal_mul hM',
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((add_lt_add hFA h7).le.trans ?_)
    linarith only [hFB, hC1]

/-- **`SvSingleCollarLogError` from its parts**: `scStageLogErrorPointwise_of_parts` and the
proved `ScStageLogDetIntegrable` (`svSingleCollarLogError_of_pointwise'`). -/
theorem svSingleCollarLogError_of_parts (hK : CollarKernelContract)
    (hMT : MatchedTracesContract) (hTU : TransmissionLengthUniformContract)
    (hRHU : RemoteHigherUniformStatement) (hWard : ScsWardScattering)
    (hMom : ScsStageLogMoment) : SvSingleCollarLogError :=
  svSingleCollarLogError_of_pointwise'
    (scStageLogErrorPointwise_of_parts hK hMT hTU hRHU hWard hMom)

/-- **`PeSameVolumeLogError` from its parts** (`peSameVolumeLogError_of_singleCollar`), from `CollarKernelContract`,
`MatchedTracesContract`, `TransmissionLengthUniformContract`, `RemoteHigherUniformStatement`, `ScsWardScattering`
and `ScsStageLogMoment`. -/
theorem peSameVolumeLogError_of_parts (hK : CollarKernelContract)
    (hMT : MatchedTracesContract) (hTU : TransmissionLengthUniformContract)
    (hRHU : RemoteHigherUniformStatement) (hWard : ScsWardScattering)
    (hMom : ScsStageLogMoment) : PeSameVolumeLogError :=
  peSameVolumeLogError_of_singleCollar
    (svSingleCollarLogError_of_parts hK hMT hTU hRHU hWard hMom)

end BlockBand.Endpoints
