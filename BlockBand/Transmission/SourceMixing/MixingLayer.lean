module

public import BlockBand.Transmission.SourceMixing.MassUpdate
public import BlockBand.Transmission.SourceMixing.TraceSpectral
public import BlockBand.Transmission.SourceMixing.OneStepMean
public import BlockBand.Transmission.PathJet.JetPathStep

/-!
# One fresh layer of the source-mixing recursions

With `F₊ = Lf₊L*`, `θ' = θ_*(1+αq/W)⁻¹` and `ρ ≥ |θ_*|`, `|θ'| ≤ ρ`. A.s. `Tr(Q₊f₊) = Tr(QF₊)` and
`‖Q₊^{1/2}f₊Q₊^{1/2}‖_HS = ‖Q^{1/2}F₊Q^{1/2}‖_HS` (`ae_traceQF_freshSchur`,
`ae_hsSandwich_freshSchur`). The excess `(G(X₊) - ρG(X) - C·e(X)q)₊` over the geometric bound, where
`e = δ₀ + δ₁ + q/W + W⁻²` and `G` is `|Tr(Qf)|` or `‖Q^{1/2}fQ^{1/2}‖_HS`, is dominated by the
centered fresh term `|Tr(Q(F₊ - EF₊))|` (resp. `‖Q^{1/2}(F₊ - EF₊)Q^{1/2}‖_HS`), whose `L^p` norm
(`p ≥ 2`) is `≤ C'q/√W` (`oneStepFluctuation` second clause, summed over an eigenbasis of `Q`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- A measurable version of `δ₁` (equal to `jetDistance1` for passive `X`). -/
def mx_jet1 (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ‖-crossTr X (boundaryZ b E) (boundaryZ b E) - s‖

/-- `e(X)·q = (δ₀ + δ₁ + q/W + W⁻²)q`. -/
def mx_err (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (jetDistance0 b E X + mx_jet1 b E s X + passiveMass b E X / W + (W : ℝ)⁻¹ ^ 2) *
    passiveMass b E X

/-- `G_tr = |Tr(Qf)|`. -/
def mx_trG (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ := ‖(passiveQ b E X * passiveF b E X).trace‖

/-- `G_hs = ‖Q^{1/2}fQ^{1/2}‖_HS`. -/
def mx_hsG (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  hsSandwich (passiveQ b E X) (passiveF b E X)

/-- The excess of `G(X₊)` over the geometric bound `ρG(X) + C·e(X)q`. -/
def mx_excess (G : Matrix (Fin W) (Fin W) ℂ → ℝ) (ρ C b E : ℝ) (s : ℂ)
    (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort) : ℝ :=
  max 0 (G (freshSchur E q.1 q.2) - ρ * G q.1 - C * mx_err b E s q.1)

theorem measurable_mx_jet1 (b E : ℝ) (s : ℂ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => mx_jet1 b E s X :=
  ((PathJet.measurable_crossTr_mat _).neg.sub measurable_const).norm

theorem measurable_mx_err (b E : ℝ) (s : ℂ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => mx_err b E s X :=
  ((((measurable_jetDistance0 b E).add (measurable_mx_jet1 b E s)).add
    ((measurable_passiveMass b E).div_const _)).add_const _).mul (measurable_passiveMass b E)

theorem measurable_mx_trG (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => mx_trG b E X := (measurable_traceQF b E).norm

theorem measurable_mx_hsG (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => mx_hsG b E X := measurable_hsQF b E

theorem measurable_mx_excess {G : Matrix (Fin W) (Fin W) ℂ → ℝ} (hG : Measurable G)
    (ρ C b E : ℝ) (s : ℂ) : Measurable (mx_excess G ρ C b E s) := by
  have h1 : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      G (freshSchur E q.1 q.2) := hG.comp (measurable_freshSchur_prod E)
  have h2 : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      ρ * G q.1 := (hG.comp measurable_fst).const_mul ρ
  have h3 : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      C * mx_err b E s q.1 := ((measurable_mx_err b E s).comp measurable_fst).const_mul C
  have h4 := (h1.sub h2).sub h3
  exact Measurable.max measurable_const h4

theorem measurable_freshTransportedF_fixed (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (freshTransportedF b E X) := by
  have hlift : Measurable fun _ : LayerSample W .oneBlockOnePort =>
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2 :
        Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) := measurable_const
  have hS : Measurable fun ω : LayerSample W .oneBlockOnePort => freshSchur E X ω :=
    Measurable.of_eval_matrix _ fun x y =>
      (PathScalar.measurable_layerSchur .oneBlockOnePort E hlift measurable_id).eval_matrix
  have hL := measurable_freshL b E X
  have hfS := (mu_measurable_passiveF (W := W) b E).comp hS
  exact Bridge.measurable_matrix_mul' (Bridge.measurable_matrix_mul' hL hfS)
    (Bridge.measurable_matrix_conjTranspose' hL)

theorem mx_jet1_eq {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (s : ℂ)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    jetDistance1 b E s X = mx_jet1 b E s X :=
  PathJet.jetDistance1_eq_crossTr hb h1 h2 s hY

theorem mx_G_nonneg_tr (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : 0 ≤ mx_trG b E X := norm_nonneg _

theorem mx_G_nonneg_hs (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : 0 ≤ mx_hsG b E X :=
  Real.sqrt_nonneg _

/-- `|θ'| ≤ ρ`. -/
theorem mx_norm_theta' {b E ρ : ℝ} {s : ℂ} (hρ : ‖thetaStar b E s‖ ≤ ρ) {α q : ℝ} (hα : 0 ≤ α)
    (hq : 0 ≤ q) : ‖thetaStar b E s / (1 + α * q / W)‖ ≤ ρ := by
  have hd : (1 : ℝ) ≤ 1 + α * q / W := by
    have : 0 ≤ α * q / W := by positivity
    linarith
  rw [norm_div, show (1 + α * q / W : ℂ) = ((1 + α * q / W : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  calc ‖thetaStar b E s‖ / (1 + α * q / W) ≤ ‖thetaStar b E s‖ / 1 :=
        div_le_div_of_nonneg_left (norm_nonneg _) one_pos hd
    _ ≤ ρ := by rw [div_one]; exact hρ

theorem mx_trace_le {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) (M : Matrix (Fin W) (Fin W) ℂ) :
    ‖(Q * M).trace‖ ≤ ‖M‖ * Q.trace.re := by
  rw [trace_mul_comm]; exact norm_trace_mul_posSemidef_le hQ M

/-- The one-layer excess bounds for `G_tr` and `G_hs`, at a fixed `p ≥ 2`. -/
theorem mx_layer (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) {s : ℂ} (hs : IsStationaryJet b E s) {ρ : ℝ}
    (hρ : ‖thetaStar b E s‖ ≤ ρ) {p : ℝ} (hp : 2 ≤ p) :
    ∃ (C C' : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        eLpNorm (fun ω => mx_excess (mx_trG b E) ρ C b E s (X, ω)) (ENNReal.ofReal p)
            (freshLaw W b) ≤ ENNReal.ofReal (C' / Real.sqrt W * passiveMass b E X) ∧
        eLpNorm (fun ω => mx_excess (mx_hsG b E) ρ C b E s (X, ω)) (ENNReal.ofReal p)
            (freshLaw W b) ≤ ENNReal.ofReal (C' / Real.sqrt W * passiveMass b E X) := by
  obtain ⟨C₁, W₁, hC₁⟩ := (oneStepMean_holds hA b hb0 hb E h1 h2).2 s hs
  obtain ⟨C₂, W₂, hC₂⟩ := oneStepFluctuation_of_passiveBounds hA b hb0 hb E h1 h2 p (by linarith)
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hα : 0 ≤ alphaCoef b E := by
    rw [alphaCoef]; have : 0 < b * etaZ b E := mul_pos hb0 hη; positivity
  refine ⟨max C₁ 0, max C₂ 0, max (max W₁ W₂) 1, le_max_right _ _, le_max_right _ _,
    fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW₂⟩, hW1⟩ := hW
  set μ := freshLaw W b
  set Q := passiveQ b E X
  set q := passiveMass b E X
  set f := passiveF b E X
  set F := freshTransportedF b E X
  set EF := matrixExpect μ F
  set θ' := thetaStar b E s / (1 + alphaCoef b E * q / W)
  set Δ := EF - θ' • f
  have hQ : Q.PosSemidef := hX.conjTranspose_mul_mul_same _
  have hq0 : 0 ≤ q := passiveMass_nonneg b E hX
  have hqtr : Q.trace.re = q := rfl
  have hθ : ‖θ'‖ ≤ ρ := by
    have := mx_norm_theta' (W := W) hρ hα hq0; simpa [θ'] using this
  have hΔ' : ‖Δ‖ * q ≤ max C₁ 0 * mx_err b E s X := by
    have h := hC₁ W hW₁ X hX
    rw [mx_jet1_eq (by linarith) h1 h2 s hX] at h
    unfold mx_err
    have he : 0 ≤ jetDistance0 b E X + mx_jet1 b E s X + q / W + (W : ℝ)⁻¹ ^ 2 := by
      have := norm_nonneg ((W : ℂ)⁻¹ * (passiveResolvent b E X).trace - matchedA E)
      have : 0 ≤ mx_jet1 b E s X := norm_nonneg _
      have : 0 ≤ q / W := by positivity
      unfold jetDistance0; positivity
    calc ‖Δ‖ * q ≤ (C₁ * (jetDistance0 b E X + mx_jet1 b E s X + q / W + (W : ℝ)⁻¹ ^ 2)) * q :=
          mul_le_mul_of_nonneg_right h hq0
      _ ≤ (max C₁ 0 * (jetDistance0 b E X + mx_jet1 b E s X + q / W + (W : ℝ)⁻¹ ^ 2)) * q := by
          gcongr; exact le_max_left _ _
      _ = _ := by ring
  -- the fluctuation bound for `Z = F - EF`
  have hB : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (F ω - EF) v) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max C₂ 0 / Real.sqrt W * vecNorm u * vecNorm v) := fun u v =>
    ((hC₂ W hW₂ X hX u v).2).trans (ENNReal.ofReal_le_ofReal (by
      have := vecNorm_nonneg u; have := vecNorm_nonneg v
      gcongr; exact le_max_left _ _))
  have hB0 : 0 ≤ max C₂ 0 / Real.sqrt W := by positivity
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]; exact ENNReal.ofReal_le_ofReal hp
  have hdec : ∀ ω, F ω = θ' • f + Δ + (F ω - EF) := fun ω => by simp only [Δ]; abel
  constructor
  · have hae := ae_traceQF_freshSchur hb0 hb hW1 h1 h2 hX
    have hbd : ∀ᵐ ω ∂μ, ‖mx_excess (mx_trG b E) ρ (max C₁ 0) b E s (X, ω)‖ ≤
        ‖(Q * (F ω - EF)).trace‖ := by
      filter_upwards [hae] with ω hω
      have hG : mx_trG b E (freshSchur E X ω) = ‖(Q * F ω).trace‖ := by
        rw [mx_trG, hω]
      have hsplit : (Q * F ω).trace = θ' * (Q * f).trace + (Q * Δ).trace + (Q * (F ω - EF)).trace := by
        nth_rewrite 1 [hdec ω]
        rw [Matrix.mul_add, Matrix.mul_add, trace_add, trace_add, Matrix.mul_smul,
          trace_smul, smul_eq_mul]
      have h1' : ‖(Q * F ω).trace‖ ≤ ρ * mx_trG b E X + max C₁ 0 * mx_err b E s X +
          ‖(Q * (F ω - EF)).trace‖ := by
        have a1 : ‖θ' * (Q * f).trace‖ ≤ ρ * mx_trG b E X := by
          rw [norm_mul, mx_trG]; exact mul_le_mul_of_nonneg_right hθ (norm_nonneg _)
        have a2 : ‖(Q * Δ).trace‖ ≤ max C₁ 0 * mx_err b E s X :=
          (mx_trace_le hQ Δ).trans (by rw [hqtr]; exact hΔ')
        rw [hsplit]
        calc ‖θ' * (Q * f).trace + (Q * Δ).trace + (Q * (F ω - EF)).trace‖
            ≤ ‖θ' * (Q * f).trace‖ + ‖(Q * Δ).trace‖ + ‖(Q * (F ω - EF)).trace‖ :=
              (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
          _ ≤ _ := by linarith
      have hex : mx_excess (mx_trG b E) ρ (max C₁ 0) b E s (X, ω) ≤ ‖(Q * (F ω - EF)).trace‖ := by
        unfold mx_excess
        exact max_le (norm_nonneg _) (by rw [hG]; linarith)
      have h0 : 0 ≤ mx_excess (mx_trG b E) ρ (max C₁ 0) b E s (X, ω) := le_max_left _ _
      exact (Real.norm_of_nonneg h0).trans_le hex
    refine (eLpNorm_mono_ae ((measurable_mx_excess (measurable_mx_trG b E) ρ (max C₁ 0) b E s).comp
      measurable_prodMk_left).aestronglyMeasurable hbd).trans ?_
    have := eLpNorm_trace_mul_le μ hQ (Z := fun ω => F ω - EF) hp1 hB0 hB
    rw [hqtr] at this; exact this
  · have hae := ae_hsSandwich_freshSchur hb0 hb hW1 h1 h2 hX
    have hbd : ∀ᵐ ω ∂μ, ‖mx_excess (mx_hsG b E) ρ (max C₁ 0) b E s (X, ω)‖ ≤
        ‖hsSandwich Q (F ω - EF)‖ := by
      filter_upwards [hae] with ω hω
      have hG : mx_hsG b E (freshSchur E X ω) = hsSandwich Q (F ω) := by rw [mx_hsG, hω]
      have h1' : hsSandwich Q (F ω) ≤ ρ * mx_hsG b E X + max C₁ 0 * mx_err b E s X +
          hsSandwich Q (F ω - EF) := by
        rw [show hsSandwich Q (F ω) = hsSandwich Q (θ' • f + Δ + (F ω - EF)) from
          congrArg _ (hdec ω)]
        have a1 : hsSandwich Q (θ' • f) ≤ ρ * mx_hsG b E X := by
          rw [hsSandwich_smul hQ, mx_hsG]
          exact mul_le_mul_of_nonneg_right hθ (Real.sqrt_nonneg _)
        have a2 : hsSandwich Q Δ ≤ max C₁ 0 * mx_err b E s X :=
          (hsSandwich_le_norm hQ Δ).trans (by rw [hqtr]; exact hΔ')
        have a3 := hsSandwich_add_le hQ (θ' • f + Δ) (F ω - EF)
        have a4 := hsSandwich_add_le hQ (θ' • f) Δ
        linarith
      have hex : mx_excess (mx_hsG b E) ρ (max C₁ 0) b E s (X, ω) ≤ hsSandwich Q (F ω - EF) := by
        unfold mx_excess
        exact max_le (Real.sqrt_nonneg _) (by rw [hG]; linarith)
      have h0 : 0 ≤ mx_excess (mx_hsG b E) ρ (max C₁ 0) b E s (X, ω) := le_max_left _ _
      exact (Real.norm_of_nonneg h0).trans_le (hex.trans (le_abs_self _))
    refine (eLpNorm_mono_ae ((measurable_mx_excess (measurable_mx_hsG b E) ρ (max C₁ 0) b E s).comp
      measurable_prodMk_left).aestronglyMeasurable hbd).trans ?_
    have hZ : Measurable fun ω => F ω - EF :=
      (measurable_freshTransportedF_fixed b E X).sub measurable_const
    have := eLpNorm_hsSandwich_le μ hQ hZ hp2 hB0 hB
    rw [hqtr] at this; exact this

end BlockBand.Transmission.SourceMixing
