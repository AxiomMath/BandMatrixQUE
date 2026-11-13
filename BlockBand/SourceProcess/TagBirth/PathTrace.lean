module

public import BlockBand.SourceProcess.TagBirth.Ward
public import BlockBand.SourceProcess.TagBirth.FreshTrace
public import BlockBand.SourceProcess.FullSource.Conversion
public import BlockBand.Transmission.LengthUniform.DeltaZero

/-!
# The tag-birth trace along the path

* `eLpNorm_le_of_fresh`: an `L^p` bound on `μ` from a bound on the fresh sections, when
  `(π, φ)` has law `μP ⊗ ν` (Fubini; `ν` a probability measure);
* `ae_past_of`, `ae_fresh_of`: a.e. statements pulled back along `π`, `φ`;
* `tagBirthTrace_of hF hδ`: the field `trace` of `TagBirthValueEnergyUniformContract`, from
  `FreshPhysTraceLp` and the T-free `δ₀` moments `DeltaZeroLengthUniform`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.TagBirth

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.LengthUniform
open scoped ENNReal ComplexOrder

section Fubini

variable {Ω P F : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace F]
  {μ : Measure Ω} {μP : Measure P} {ν : Measure F} {π : Ω → P} {φ : Ω → F}

theorem ae_past_of [IsProbabilityMeasure ν] (hπ : Measurable π) (hφ : Measurable φ)
    (hmap : μ.map (fun ω => (π ω, φ ω)) = μP.prod ν) {Q : P → Prop} (h : ∀ᵐ q ∂μP, Q q) :
    ∀ᵐ ω ∂μ, Q (π ω) := by
  have e : μ.map π = μP := by
    rw [show π = Prod.fst ∘ fun ω => (π ω, φ ω) from rfl,
      ← Measure.map_map measurable_fst (hπ.prodMk hφ), hmap, Measure.map_fst_prod, measure_univ,
      one_smul]
  exact ae_of_ae_map hπ.aemeasurable (by rw [e]; exact h)

theorem ae_fresh_of [IsProbabilityMeasure μP] [SFinite ν] (hπ : Measurable π) (hφ : Measurable φ)
    (hmap : μ.map (fun ω => (π ω, φ ω)) = μP.prod ν) {Q : F → Prop} (h : ∀ᵐ x ∂ν, Q x) :
    ∀ᵐ ω ∂μ, Q (φ ω) := by
  have e : μ.map φ = ν := by
    rw [show φ = Prod.snd ∘ fun ω => (π ω, φ ω) from rfl,
      ← Measure.map_map measurable_snd (hπ.prodMk hφ), hmap, Measure.map_snd_prod, measure_univ,
      one_smul]
  exact ae_of_ae_map hφ.aemeasurable (by rw [e]; exact h)

/-- **`L^p` from the fresh sections.** -/
theorem eLpNorm_le_of_fresh [SFinite μP] [IsProbabilityMeasure ν] (hπ : Measurable π)
    (hφ : Measurable φ) (hmap : μ.map (fun ω => (π ω, φ ω)) = μP.prod ν) {p : ℝ} (hp : 0 < p)
    {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) {Fn : P × F → ℝ} (hFn : Measurable Fn)
    {g : P → ℝ} (hg : Measurable g) (hpt : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ Fn (π ω, φ ω))
    (hstep : ∀ᵐ q ∂μP, eLpNorm (fun x => Fn (q, x)) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (g q)) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ eLpNorm (fun ω => g (π ω)) (ENNReal.ofReal p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt' : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgm : AEStronglyMeasurable (fun ω => g (π ω)) μ := (hg.comp hπ).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt' hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt' hgm,
    ENNReal.toReal_ofReal hp.le]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have h := lintegral_indicator_step (μ := μ) (μP := μP) (ν := ν) hπ hφ hmap MeasurableSet.univ
    (Φ := fun q => ‖Fn q‖ₑ ^ p) (hFn.enorm.pow_const _) (Ψ := fun q => ‖g q‖ₑ ^ p)
    (hg.enorm.pow_const _) (Z := fun ω => ‖f ω‖ₑ ^ p) (hpt.mono fun ω h _ => by
      refine ENNReal.rpow_le_rpow ?_ hp.le
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (h.trans (Real.le_norm_self _)))
    (hstep.mono fun q hq _ => by
      have hm : Measurable fun x => Fn (q, x) := hFn.comp measurable_prodMk_left
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt' hm.aestronglyMeasurable,
        ENNReal.toReal_ofReal hp.le, one_div, ENNReal.rpow_inv_le_iff hp] at hq
      refine hq.trans (ENNReal.rpow_le_rpow ?_ hp.le)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (Real.le_norm_self _))
  simpa using h

end Fubini

variable {W : ℕ}

theorem measurable_physTr_past (b E : ℝ) (k : ℕ) :
    Measurable fun q : PastSample W k × LayerSample W .oneBlockOnePort =>
      physTr b E (nearSchur (boundaryZ b E) (pastXX E W k q.1)) q.2 := by
  have hX : Measurable fun q : PastSample W k × LayerSample W .oneBlockOnePort =>
      nearSchur (boundaryZ b E) (pastXX E W k q.1) :=
    (measurable_nearSchur_comp _ (measurable_pastXX E k)).comp measurable_fst
  have h := measurable_trace_comp (measurable_freshBlock_comp b E hX measurable_snd true true)
  exact measurable_const.mul h

theorem aesm_tagTrace (b E : ℝ) (j k : ℕ) (c : ℂ) :
    AEStronglyMeasurable (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace - c)
      (growthPathLaw W b) := by
  have e : (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace - c) = fun ω =>
      (W : ℂ)⁻¹ * ((pastS b E W j k (pastCoords W j ω))ᴴ *
        pastS b E W j k (pastCoords W j ω)).trace - c := by
    funext ω; rw [tagResponse_eq_factor]
  rw [e]
  have hS := (measurable_pastS (W := W) b E j k).comp (measurable_pastCoords W j)
  exact ((measurable_const.mul (measurable_trace_comp
    (measurable_matrix_mul' (measurable_matrix_conjTranspose' hS) hS))).sub
      measurable_const).aestronglyMeasurable

/-- **The field `trace`** of `TagBirthValueEnergyUniformContract`. -/
theorem tagBirthTrace_of (hF : FreshPhysTraceLp) (hδ : DeltaZeroLengthUniform) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ ε T p : ℝ, 0 < ε → ε < T →
    1 ≤ p → ∀ θ : ℝ, 0 < θ → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : ℕ, ε * W ≤ k → ((k + 1 : ℕ) : ℝ) ≤ T * W →
        eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W (k + 1) k ω).trace - (dStar b : ℂ))
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal θ := by
  intro b hb0 hb κ hκ ε T p hε _ hp θ hθ
  obtain ⟨A, B, W₁, hA, hB, hF'⟩ := hF b hb0 hb κ hκ p hp
  obtain ⟨C, hC, hδ'⟩ := hδ b hb0 hb κ p hκ hp
  obtain ⟨W₂, hδ''⟩ := hδ' T
  set ηi := (etaLow b κ)⁻¹
  have hηL := etaLow_pos (b := b) (by linarith) hκ
  have hηi : 0 ≤ ηi := inv_nonneg.mpr hηL.le
  set K := ηi * (A * C + B) / θ
  refine ⟨max (max W₁ W₂) (⌈K ^ 2⌉₊ + 1), fun W hW E hE k hk hkT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW₂⟩, hW₃⟩ := hW
  have hW1 : 1 ≤ W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hηle : (etaZ b E)⁻¹ ≤ ηi := inv_anti₀ hηL (etaLow_le (by linarith) hκ hE)
  have hk1 : 1 ≤ k := by
    have : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk
    exact_mod_cast this
  have hkT' : (k : ℝ) ≤ T * W := by push_cast at hkT; linarith
  set π := pastCoords W k
  set φ := freshSample W k
  have hmap := growthPathLaw_map_past_fresh W k b
  set Fn : PastSample W k × LayerSample W .oneBlockOnePort → ℝ := fun q =>
    ηi * ‖physTr b E (nearSchur (boundaryZ b E) (pastXX E W k q.1)) q.2 - matchedA E‖
  set g : PastSample W k → ℝ := fun q =>
    ηi * (A * jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W k q)) + B / Real.sqrt W)
  have hFn : Measurable Fn :=
    measurable_const.mul ((measurable_physTr_past b E k).sub measurable_const).norm
  have hg : Measurable g := by
    refine measurable_const.mul ((measurable_const.mul ?_).add measurable_const)
    exact (measurable_jetDistance0 b E).comp (measurable_nearSchur_comp _ (measurable_pastXX E k))
  have hpt : ∀ᵐ ω ∂growthPathLaw W b,
      ‖(W : ℂ)⁻¹ * (tagResponse b E W (k + 1) k ω).trace - (dStar b : ℂ)‖ ≤ Fn (π ω, φ ω) := by
    filter_upwards [ae_tagResponse_succ_new_full hb0 hb h1 h2 hW1,
      ae_past_of (measurable_pastCoords W k) (measurable_freshSample W k) hmap
        (ae_pastLaw_hermitian W k b),
      ae_fresh_of (measurable_pastCoords W k) (measurable_freshSample W k) hmap
        (BlockBand.Transmission.PassiveLayer.ae_good W hb0 hW1)] with ω hY hH hG
    rw [hY k hk1, pastXX_eq]
    refine (norm_birthTrace_sub_le hb h1 h2 (pastXX_isHermitian E hH) hG.1 hG.2).trans ?_
    exact mul_le_mul_of_nonneg_right hηle (norm_nonneg _)
  have hstep : ∀ᵐ q ∂pastLaw W k b,
      eLpNorm (fun x => Fn (q, x)) (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (g q) := by
    filter_upwards [ae_pastLaw_hermitian W k b] with q hq
    have hYq := nearSchur_passive (etaZ_pos b E (by linarith) h1 h2) (pastXX_isHermitian E hq)
    have hm : AEStronglyMeasurable (fun x => physTr b E (nearSchur (boundaryZ b E)
        (pastXX E W k q)) x - matchedA E) (freshLaw W b) :=
      (((measurable_physTr_past b E k).comp measurable_prodMk_left).sub
        measurable_const).aestronglyMeasurable
    have e : (fun x => Fn (q, x)) = ηi • fun x => ‖physTr b E (nearSchur (boundaryZ b E)
        (pastXX E W k q)) x - matchedA E‖ := by funext x; simp [Fn]
    rw [e, eLpNorm_const_smul, eLpNorm_norm _ hm, ← ofReal_norm, Real.norm_of_nonneg hηi]
    refine (mul_le_mul_right (hF' W hW₁ E hE _ hYq) _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hηi]
  refine (eLpNorm_le_of_fresh (measurable_pastCoords W k) (measurable_freshSample W k) hmap
    (by linarith) (aesm_tagTrace b E (k + 1) k _) hFn hg hpt hstep).trans ?_
  -- the past: `‖g(π)‖_p ≤ ηi(A‖δ₀‖_p + B/√W)`
  have hgπ : (fun ω => g (π ω)) = ηi • ((fun ω => A * jetDistance0 b E (pathX b E W k ω)) +
      fun _ => B / Real.sqrt W) := by
    funext ω; simp [g, π, pathX_eq_past]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using hp
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hδk := hδ'' W hW₂ E hE k hk1 hkT'
  rw [hgπ, eLpNorm_const_smul]
  refine (mul_le_mul_right (eLpNorm_add_le hp1) _).trans ?_
  rw [eLpNorm_const_prob _ hp0, show (fun ω => A * jetDistance0 b E (pathX b E W k ω)) =
    A • fun ω => jetDistance0 b E (pathX b E W k ω) from rfl, eLpNorm_const_smul]
  refine (mul_le_mul_right (add_le_add (mul_le_mul_right hδk _) le_rfl) _).trans ?_
  rw [Real.enorm_of_nonneg hηi, Real.enorm_of_nonneg hA,
    Real.enorm_of_nonneg (show 0 ≤ B / Real.sqrt W by positivity), ← ENNReal.ofReal_mul hA,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hηi]
  refine ENNReal.ofReal_le_ofReal ?_
  -- arithmetic: `ηi(AC/W + B/√W) ≤ ηi(AC + B)/√W ≤ θ`
  have hs1 : 1 ≤ Real.sqrt W := by rw [Real.one_le_sqrt]; exact_mod_cast hW1
  have hWs : 1 / (W : ℝ) ≤ 1 / Real.sqrt W := one_div_le_one_div_of_le hsW
    (by nlinarith [Real.mul_self_sqrt hW0.le])
  have hKs : K ≤ Real.sqrt W := by
    have h3 : K ^ 2 < W := by
      have := Nat.le_ceil (K ^ 2)
      have h4 : ((⌈K ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW₃
      push_cast at h4; linarith
    exact le_of_lt (Real.lt_sqrt_of_sq_lt h3)
  have hK0 : 0 ≤ ηi * (A * C + B) := by positivity
  calc ηi * (A * (C / W) + B / Real.sqrt W)
      ≤ ηi * ((A * C + B) * (1 / Real.sqrt W)) := by
        refine mul_le_mul_of_nonneg_left ?_ hηi
        have : C / W = C * (1 / W) := by ring
        rw [this]
        have e2 : B / Real.sqrt W = B * (1 / Real.sqrt W) := by ring
        rw [e2]
        nlinarith [mul_le_mul_of_nonneg_left hWs (mul_nonneg hA hC)]
    _ = ηi * (A * C + B) / Real.sqrt W := by ring
    _ ≤ θ := by
        rw [div_le_iff₀ hsW]
        have : ηi * (A * C + B) = K * θ := by simp only [K]; field_simp
        rw [this]
        nlinarith

end BlockBand.SourceProcess.TagBirth
