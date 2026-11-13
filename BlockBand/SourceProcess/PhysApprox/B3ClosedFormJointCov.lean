module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormJointLead

/-!
# The mixed `(𝒦, Gram)` pairs of `CovLayerHyp` (`CovLayerHypKG`)

* `incr_zero`, `incr_one`: the one-layer Gram increments at a chain state are `c_k*(NN* - 1)c_l`
  and `c_k*(NPN* - P)c_l`;
* `sigmaPlus_mul_star_cZero`: `σ₊ conj(-c₀) = -iηD₀`;
* **The hypothesis `B3ClosedChainNearPin`**: `B3ClosedChainPin` together with the near-rows
  clause `ι𝕊(𝕏_j)V_j = ιP𝕊_clV_j` on the alive set (for the Cayley state `b3ChainXX` this is
  `twoPortScattering_b3ChainXX`, `nearPortProj_mul_b3PadScatter`,
  `A_mul_b3ClosedFrameAt`, given `B3PadInvertible`; it is proved from `B3PadTransportZ` by
  `B3LayerMean.b3ClosedChainNearPin_of_z` and `b3PadTransportZ_holds`);
* **`covLayerAt_mixed_step`**: one step, from the two joint one-layer lemmas;
* **`covLayerHypKG_of_near`**: `CovLayerHypKG b3CovErr b3CovZ` from the Gaussian inputs,
  `FreshDeltaQuadCov` and `B3ClosedChainNearPin`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedSummedProof (incr layerGram)
open BlockBand.SourceProcess.FullSource (wardF)
open BlockBand.SourceProcess.FullSourceCovariance (covErr)
open BlockBand.SourceProcess.ContractingWords (currentOf)
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

variable {W np K : ℕ}

/-! ## The one-layer Gram increments -/

theorem incr_zero (b E : ℝ) {c : Type} [Fintype c] [DecidableEq c]
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (V : Matrix (Fin 2 × Fin W) c ℂ) (k l : c)
    (f : LayerSample W .oneBlockOnePort) :
    incr b E XX V (0, k, l) f =
      bilinear (fun a => V a k) (wardNoise b E XX f) (fun a => V a l) := by
  rw [bilinear, ← entry_eq_dot]
  simp only [incr, layerGram, gramEntry, gramPair, sourceGram, wardNoise, ↓reduceIte,
    conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.sub_apply, Matrix.mul_assoc]

theorem incr_one (b E : ℝ) {c : Type} [Fintype c] [DecidableEq c]
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (V : Matrix (Fin 2 × Fin W) c ℂ) (k l : c)
    (f : LayerSample W .oneBlockOnePort) :
    incr b E XX V (1, k, l) f =
      bilinear (fun a => V a k) (freshTransport b E XX f * nearProjection W *
        (freshTransport b E XX f)ᴴ - nearProjection W) (fun a => V a l) := by
  rw [bilinear, ← entry_eq_dot]
  simp only [incr, layerGram, gramEntry, gramPair, nearGram, one_ne_zero, ↓reduceIte,
    conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.sub_apply, Matrix.mul_assoc]

/-! ## The scalar of the bracket -/

theorem sigmaPlus_mul_star_cZero {b E : ℝ} (hb0 : 0 < b) (hE1 : -2 < E) (hE2 : E < 2)
    (hη : 0 < etaZ b E) :
    ((sigmaPlus b : ℝ) : ℂ) * star (-cZero b E) =
      -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) := by
  rw [BlockBand.Transmission.PassiveCovariance.sigmaPlus_eq b E hb0 hE1 hE2, cZero]
  have hη0 : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  simp only [star_neg, star_inv₀, star_mul', Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## The fresh integrability -/

theorem norm_mul_le_sq_add_sq (a c : ℂ) : ‖a * c‖ ≤ ‖a‖ ^ 2 + ‖c‖ ^ 2 := by
  rw [norm_mul]; nlinarith [sq_nonneg (‖a‖ - ‖c‖), norm_nonneg a, norm_nonneg c]

/-- `E_f|(u*Δv)·incr| ≤ r⁴C₂² + 2R'²(C₄ + 1)`. -/
theorem lintegral_dK_incr_le {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {c : Type} [Fintype c] [DecidableEq c]
    {u v : Fin W → ℂ} {r C₂ C₄ R' : ℝ} (hu : vecNorm u ≤ r) (hv : vecNorm v ≤ r)
    (hΔ : ∫⁻ f, ENNReal.ofReal (‖freshDelta b E X f‖ ^ 2) ∂freshLaw W b ≤
      ENNReal.ofReal (C₂ ^ 2))
    (h4 : ∫ y, ‖freshTransport b E XX y‖ ^ 4 ∂freshLaw W b ≤ C₄)
    (h4i : Integrable (fun y => ‖freshTransport b E XX y‖ ^ 4) (freshLaw W b))
    (V : Matrix (Fin 2 × Fin W) c ℂ) (hR' : 0 ≤ R') (hR : (Vᴴ * V).trace.re ≤ R')
    (g : Fin 2 × c × c) :
    ∫⁻ f, ‖bilinear u (freshDelta b E X f) v * incr b E XX V g f‖ₑ ∂freshLaw W b ≤
      ENNReal.ofReal (r ^ 4 * C₂ ^ 2) + ENNReal.ofReal (2 * R' ^ 2 * (C₄ + 1)) := by
  have hr : 0 ≤ r := (Transmission.PassiveCovariance.vecNorm_nonneg u).trans hu
  have hI := ClosedSummedProof.lintegral_incr_mul_le h4 h4i V hR' hR g g
  have hpt : ∀ f, ‖bilinear u (freshDelta b E X f) v * incr b E XX V g f‖ₑ ≤
      ENNReal.ofReal (r ^ 4) * ENNReal.ofReal (‖freshDelta b E X f‖ ^ 2) +
        ‖incr b E XX V g f * incr b E XX V g f‖ₑ := by
    intro f
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((norm_mul_le_sq_add_sq _ _).trans ?_)
    have hb := Transmission.PassiveCovariance.norm_bilinear_le u (freshDelta b E X f) v
    have hb' : ‖bilinear u (freshDelta b E X f) v‖ ≤ r ^ 2 * ‖freshDelta b E X f‖ := by
      have h0 := Transmission.PassiveCovariance.vecNorm_nonneg u
      have h1 := Transmission.PassiveCovariance.vecNorm_nonneg v
      have h2 := norm_nonneg (freshDelta b E X f)
      nlinarith [mul_le_mul hu hv h1 hr]
    have hsq : ‖bilinear u (freshDelta b E X f) v‖ ^ 2 ≤ r ^ 4 * ‖freshDelta b E X f‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hb' 2
      nlinarith
    rw [norm_mul, ← sq]
    linarith
  refine (lintegral_mono hpt).trans ?_
  have hm : Measurable fun f => incr b E XX V g f :=
    (ClosedSummedProof.measurable_layerGramEntry b E measurable_const measurable_const
      measurable_id g).sub measurable_const
  have hmm : AEMeasurable (fun f => ‖incr b E XX V g f * incr b E XX V g f‖ₑ) (freshLaw W b) :=
    (hm.mul hm).enorm.aemeasurable
  rw [lintegral_add_right' _ hmm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine add_le_add ?_ hI
  calc ENNReal.ofReal (r ^ 4) * ∫⁻ f, ENNReal.ofReal (‖freshDelta b E X f‖ ^ 2) ∂freshLaw W b
      ≤ ENNReal.ofReal (r ^ 4) * ENNReal.ofReal (C₂ ^ 2) := by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

/-! ## Column and norm helpers -/

theorem col_mul_eq {c : Type*} [Fintype c] (M : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix (Fin 2 × Fin W) c ℂ) (d : c) :
    (fun x => (M * V) x d) = M *ᵥ fun a => V a d := by
  funext x; simp [Matrix.mul_apply, mulVec, dotProduct]

theorem vecNorm_col_le {c : Type*} [Fintype c] (V : Matrix (Fin 2 × Fin W) c ℂ) (d : c)
    {R : ℝ} (hR : (Vᴴ * V).trace.re < R) : vecNorm (fun a => V a d) ≤ Real.sqrt R :=
  Real.sqrt_le_sqrt ((col_sq_le_trace V d).trans hR.le)

/-! ## The near-rows chain hypothesis -/

/-- **The hypothesis `B3ClosedChainNearPin`**: the closed chain (`B3ClosedChainAt`) with the
near-rows clause `ι𝕊(𝕏_j)V_j = ιP𝕊_clV_j` a.e. on the alive set (the chain's near outgoing rows
are the closed ones). For the Cayley state `b3ChainXX` it follows from
`twoPortScattering_b3ChainXX`, `nearPortProj_mul_b3PadScatter` and `A_mul_b3ClosedFrameAt`
under `B3PadInvertible`. -/
def B3ClosedChainNearPin : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∃ XX : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        B3ClosedChainAt b E s h τ m R W j (Vs W) XX C ∧
        ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
          nearSel W * twoPortScattering b E (XX y) * b3ClosedFrameAt b E s h τ m W j (Vs W) y =
            nearSel W * b3ClosedPS b E s h W j y.1.1 (phase y.2) *
              b3ClosedFrameAt b E s h τ m W j (Vs W) y

/-! ## The arithmetic and the fresh evaluation at one sample -/

theorem mixed_arith {I L1 L2 : ℂ} {A a w ce δ2 e Z : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (he : 0 ≤ e)
    (hZ : 0 ≤ Z) (hw : 0 ≤ w) (h1 : ‖I - (L1 + L2)‖ ≤ A * (w + ce + δ2)) (hce : ce ≤ w + e ^ 2)
    (hδ : δ2 ≤ e ^ 2) (h2 : ‖L1‖ ≤ a * (e * Z)) :
    ‖I - L2‖ ≤ (2 * A + a) * (e * Z) + (2 * A + a) * (w + e ^ 2 + e ^ 2) := by
  have e1 : I - L2 = (I - (L1 + L2)) + L1 := by ring
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  have k1 : A * (w + ce + δ2) ≤ 2 * A * (w + e ^ 2 + e ^ 2) := by
    have : 2 * A * (w + e ^ 2 + e ^ 2) = A * (2 * (w + e ^ 2 + e ^ 2)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg e]) hA
  have k2 : 0 ≤ 2 * A * (e * Z) := by positivity
  have k3 : 0 ≤ a * (w + e ^ 2 + e ^ 2) := by positivity
  have e2 : (2 * A + a) * (e * Z) + (2 * A + a) * (w + e ^ 2 + e ^ 2) =
      2 * A * (e * Z) + a * (e * Z) + 2 * A * (w + e ^ 2 + e ^ 2) + a * (w + e ^ 2 + e ^ 2) := by
    ring
  rw [e2]
  linarith

/-- **The mixed bracket at one sample**: the fresh integral of `(u*Δv)·incr_g` at a Hermitian
chain state is `W⁻¹ kGramCov` up to the `CovLayerHyp` error, from the two joint one-layer
lemmas at that state. -/
theorem mixed_eval {b E : ℝ} (hb0 : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) (hη : 0 < etaZ b E)
    {W : ℕ} (hW1 : 1 ≤ W) (XY : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hH : XY.IsHermitian)
    (V : Matrix (Fin 2 × Fin W) (SrcCol K (Fin np)) ℂ)
    (hcur : currentOf b E XY = V * srcSignature K (Fin np) * Vᴴ) (u v : Fin W → ℂ)
    (ij : Fin np × Fin np) {r : ℝ} (hr : 0 ≤ r) (hu : vecNorm u ≤ r) (hvn : vecNorm v ≤ r)
    (hcol : ∀ d, vecNorm (fun a => V a d) ≤ r)
    (hu_eq : u = nearSel W *ᵥ fun a => V a (Sum.inr ij.1))
    (hv_eq : v = nearSel W *ᵥ (twoPortScattering b E XY *ᵥ fun a => V a (Sum.inr ij.2)))
    {CJ : ℝ}
    (hJ0 : ∀ (u v : Fin W → ℂ) (c c' : Fin 2 × Fin W → ℂ) (Cf : ℝ), vecNorm u ≤ Cf →
        vecNorm v ≤ Cf → vecNorm (nearSel W *ᵥ c) ≤ Cf → vecNorm (nearSel W *ᵥ c') ≤ Cf →
        vecNorm (wardF b E XY *ᵥ c) ≤ Cf → vecNorm (wardF b E XY *ᵥ c') ≤ Cf →
        ‖∫ F, bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XY) F) v *
              bilinear c (wardNoise b E XY F) c' ∂freshLaw W b -
            (sigmaMinus b E (b3Jet b E) / W *
                crossedTensor u v (nearSel W *ᵥ c) (wardF b E XY *ᵥ c') 1 1 +
              ((sigmaPlus b : ℝ) : ℂ) / W *
                (bilinear u 1 (nearSel W *ᵥ c') * bilinear (wardF b E XY *ᵥ c) 1 v))‖ ≤
          CJ * Cf ^ 4 * (covErr b E (b3Jet b E) (nearSchur (boundaryZ b E) XY) +
            (jetDistance0 b E (nearSchur (boundaryZ b E) XY) + (W : ℝ)⁻¹) ^ 2))
    (hJ1 : ∀ (u v : Fin W → ℂ) (c c' : Fin 2 × Fin W → ℂ) (Cf : ℝ), vecNorm u ≤ Cf →
        vecNorm v ≤ Cf → vecNorm (nearSel W *ᵥ c) ≤ Cf → vecNorm (nearSel W *ᵥ c') ≤ Cf →
        vecNorm (passiveF b E (nearSchur (boundaryZ b E) XY) *ᵥ (nearSel W *ᵥ c)) ≤ Cf →
        vecNorm (passiveF b E (nearSchur (boundaryZ b E) XY) *ᵥ (nearSel W *ᵥ c')) ≤ Cf →
        ‖∫ F, bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XY) F) v *
              bilinear c (freshTransport b E XY F * nearProjection W *
                (freshTransport b E XY F)ᴴ - nearProjection W) c' ∂freshLaw W b -
            (sigmaMinus b E (b3Jet b E) / W * crossedTensor u v (nearSel W *ᵥ c)
                (passiveF b E (nearSchur (boundaryZ b E) XY) *ᵥ (nearSel W *ᵥ c')) 1 1 +
              ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear u 1 (nearSel W *ᵥ c') *
                bilinear (passiveF b E (nearSchur (boundaryZ b E) XY) *ᵥ (nearSel W *ᵥ c)) 1 v))‖
          ≤ CJ * Cf ^ 4 * ((W : ℝ)⁻¹ / Real.sqrt W +
            covErr b E (b3Jet b E) (nearSchur (boundaryZ b E) XY) +
            (jetDistance0 b E (nearSchur (boundaryZ b E) XY) + (W : ℝ)⁻¹) ^ 2))
    (hCJ : 0 ≤ CJ) {e : ℝ} (hWe : (W : ℝ)⁻¹ ≤ e)
    (hδ : (jetDistance0 b E (nearSchur (boundaryZ b E) XY) + (W : ℝ)⁻¹) ^ 2 ≤ e ^ 2)
    (hcov : covErr b E (b3Jet b E) (nearSchur (boundaryZ b E) XY) ≤
      (W : ℝ)⁻¹ / Real.sqrt W + e ^ 2)
    {Zv : ℝ} (hZ0 : 0 ≤ Zv) (hQZ : ∀ k, ‖bilinear (nearSel W *ᵥ fun a => V a k) 1 v‖ ≤ Zv)
    (g : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    ‖∫ f, bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XY) f) v *
        incr b E XY V g f ∂freshLaw W b -
      (W : ℂ)⁻¹ * kGramCov b E ij g (Vᴴ * V, Vᴴ * nearPortProj W * V)‖ ≤
      (2 * (CJ * ((1 + ‖cZero b E‖) * r) ^ 4) +
        ‖sigmaMinus b E (b3Jet b E)‖ * ‖cZero b E‖ * r ^ 2) * (e * Zv) +
      (2 * (CJ * ((1 + ‖cZero b E‖) * r) ^ 4) +
        ‖sigmaMinus b E (b3Jet b E)‖ * ‖cZero b E‖ * r ^ 2) *
        ((W : ℝ)⁻¹ / Real.sqrt W + e ^ 2 + e ^ 2) := by
  set c0 := ‖cZero b E‖
  have hc0 : 0 ≤ c0 := norm_nonneg _
  set Cf := (1 + c0) * r
  have hrCf : r ≤ Cf := le_mul_of_one_le_left hr (by linarith)
  have hc0Cf : c0 * r ≤ Cf := mul_le_mul_of_nonneg_right (by linarith) hr
  set σm := ‖sigmaMinus b E (b3Jet b E)‖
  have hσm : 0 ≤ σm := norm_nonneg _
  have he0 : 0 ≤ e := (by positivity : (0:ℝ) ≤ (W:ℝ)⁻¹).trans hWe
  have hw3 : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by positivity
  have hCf4 : 0 ≤ CJ * Cf ^ 4 := by positivity
  have hrem : ∀ (w : Fin W → ℂ) (k : SrcCol K (Fin np)), vecNorm w ≤ c0 * r →
      ‖sigmaMinus b E (b3Jet b E) / W * crossedTensor u v (nearSel W *ᵥ fun a => V a k) w 1 1‖ ≤
        σm * c0 * r ^ 2 * (e * Zv) := by
    intro w k hw
    simp only [crossedTensor, norm_mul, norm_div, Complex.norm_natCast]
    have h1 : ‖bilinear u 1 w‖ ≤ r * (c0 * r) := by
      rw [bilinear_one]
      exact (Transmission.PassiveCovariance.norm_star_dotProduct_le u w).trans
        (mul_le_mul hu hw (Transmission.PassiveCovariance.vecNorm_nonneg _) hr)
    have h2 := hQZ k
    calc σm / W * (‖bilinear u 1 w‖ * ‖bilinear (nearSel W *ᵥ fun a => V a k) 1 v‖)
        ≤ σm * e * (r * (c0 * r) * Zv) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hWe hσm)
            (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (by positivity)
            (mul_nonneg hσm he0)
      _ = σm * c0 * r ^ 2 * (e * Zv) := by ring
  have harith := fun (I L1 L2 : ℂ) (h1 : ‖I - (L1 + L2)‖ ≤ CJ * Cf ^ 4 * ((W : ℝ)⁻¹ /
      Real.sqrt W + covErr b E (b3Jet b E) (nearSchur (boundaryZ b E) XY) +
      (jetDistance0 b E (nearSchur (boundaryZ b E) XY) + (W : ℝ)⁻¹) ^ 2))
      (h2 : ‖L1‖ ≤ σm * c0 * r ^ 2 * (e * Zv)) =>
    mixed_arith (I := I) (L1 := L1) (L2 := L2) hCf4 (by positivity) he0 hZ0 hw3 h1 hcov hδ h2
  obtain ⟨σ, k, l⟩ := g
  obtain rfl | rfl : σ = 0 ∨ σ = 1 := by fin_cases σ <;> simp
  · -- `dM`
    have hI : ∀ f, bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XY) f) v *
        incr b E XY V ((0 : Fin 2), k, l) f =
          bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XY) f) v *
            bilinear (fun a => V a k) (wardNoise b E XY f) (fun a => V a l) := fun f => by
      rw [incr_zero]
    have hw : ∀ d, vecNorm (wardF b E XY *ᵥ fun a => V a d) ≤ c0 * r := fun d => by
      rw [wardF_eq hη, smul_mulVec, ← mulVec_mulVec,
        Transmission.PassiveCovariance.vecNorm_smul', norm_neg]
      exact mul_le_mul_of_nonneg_left
        ((vecNorm_nearSel_scattering_le hη hH _).trans (hcol d)) hc0
    have hJ := hJ0 u v (fun a => V a k) (fun a => V a l) Cf (hu.trans hrCf)
      (hvn.trans hrCf) ((vecNorm_nearSel_le _).trans ((hcol k).trans hrCf))
      ((vecNorm_nearSel_le _).trans ((hcol l).trans hrCf)) ((hw k).trans hc0Cf)
      ((hw l).trans hc0Cf)
    have hL2 : ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear u 1 (nearSel W *ᵥ fun a => V a l) *
        bilinear (wardF b E XY *ᵥ fun a => V a k) 1 v) =
        (W : ℂ)⁻¹ * kGramCov b E ij ((0 : Fin 2), k, l) (Vᴴ * V, Vᴴ * nearPortProj W * V) := by
      rw [hu_eq, lead_u, hv_eq, lead_dM hη hcur]
      simp only [kGramCov, ↓reduceIte]
      rw [div_eq_mul_inv, ← sigmaPlus_mul_star_cZero hb0 hE1 hE2 hη]
      ring
    rw [integral_congr_ae (Eventually.of_forall hI), ← hL2]
    exact harith _ _ _ (hJ.trans (mul_le_mul_of_nonneg_left (by linarith) hCf4))
      (hrem _ k (hw l))
  · -- `dB`
    have hI : ∀ f, bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XY) f) v *
        incr b E XY V ((1 : Fin 2), k, l) f =
          bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XY) f) v *
            bilinear (fun a => V a k) (freshTransport b E XY f * nearProjection W *
              (freshTransport b E XY f)ᴴ - nearProjection W) (fun a => V a l) := fun f => by
      rw [incr_one]
    have hw : ∀ d, vecNorm (passiveF b E (nearSchur (boundaryZ b E) XY) *ᵥ
        (nearSel W *ᵥ fun a => V a d)) ≤ c0 * r := fun d => by
      rw [passiveF_nearSchur hη hH, smul_mulVec, Transmission.PassiveCovariance.vecNorm_smul',
        norm_neg, ← mulVec_mulVec, ← mulVec_mulVec]
      refine mul_le_mul_of_nonneg_left ((vecNorm_nearSel_scattering_le hη hH _).trans ?_) hc0
      rw [vecNorm_nearSel_conj]
      exact (vecNorm_nearSel_le _).trans (hcol d)
    have hJ := hJ1 u v (fun a => V a k) (fun a => V a l) Cf (hu.trans hrCf)
      (hvn.trans hrCf) ((vecNorm_nearSel_le _).trans ((hcol k).trans hrCf))
      ((vecNorm_nearSel_le _).trans ((hcol l).trans hrCf)) ((hw k).trans hc0Cf)
      ((hw l).trans hc0Cf)
    have hL2 : ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear u 1 (nearSel W *ᵥ fun a => V a l) *
        bilinear (passiveF b E (nearSchur (boundaryZ b E) XY) *ᵥ
          (nearSel W *ᵥ fun a => V a k)) 1 v) =
        (W : ℂ)⁻¹ * kGramCov b E ij ((1 : Fin 2), k, l) (Vᴴ * V, Vᴴ * nearPortProj W * V) := by
      rw [hu_eq, lead_u, hv_eq, lead_dB hη hH hcur (srcSignature_conjTranspose K (Fin np))]
      simp only [kGramCov, one_ne_zero, ↓reduceIte]
      rw [div_eq_mul_inv, ← sigmaPlus_mul_star_cZero hb0 hE1 hE2 hη]
      ring
    rw [integral_congr_ae (Eventually.of_forall hI), ← hL2]
    exact harith _ _ _ hJ (hrem _ k (hw l))

/-! ## One step -/

/-- **The mixed `(𝒦, Gram)` bracket at one step**, from the two joint one-layer lemmas (as
hypotheses `hJ0`, `hJ1` at this `W`, `E`), a chain state with the near-rows clause, and the fresh
moment bounds. -/
theorem covLayerAt_mixed_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) {κ : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) (s h : ℝ) (hh : h ^ 2 < 1)
    (τ m : Fin np → ℝ) (R : ℝ) {W : ℕ} (hW1 : 1 ≤ W) {T : ℝ} {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ∈ genNoBirthSteps s T τ W)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs)
    {XX : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {Cch : ℝ}
    (hch : B3ClosedChainAt b E s h τ m R W j Vs XX Cch)
    (hnear : ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
      nearSel W * twoPortScattering b E (XX y) * b3ClosedFrameAt b E s h τ m W j Vs y =
        nearSel W * b3ClosedPS b E s h W j y.1.1 (phase y.2) * b3ClosedFrameAt b E s h τ m W j Vs y)
    {CJ C₂ C₄ : ℝ} (hCJ : 0 ≤ CJ) (hC₄ : 0 ≤ C₄)
    (hJ0 : ∀ X' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X'.IsHermitian →
      ∀ (u v : Fin W → ℂ) (c c' : Fin 2 × Fin W → ℂ) (Cf : ℝ), vecNorm u ≤ Cf →
        vecNorm v ≤ Cf → vecNorm (nearSel W *ᵥ c) ≤ Cf → vecNorm (nearSel W *ᵥ c') ≤ Cf →
        vecNorm (wardF b E X' *ᵥ c) ≤ Cf → vecNorm (wardF b E X' *ᵥ c') ≤ Cf →
        ‖∫ F, bilinear u (freshDelta b E (nearSchur (boundaryZ b E) X') F) v *
              bilinear c (wardNoise b E X' F) c' ∂freshLaw W b -
            (sigmaMinus b E (b3Jet b E) / W *
                crossedTensor u v (nearSel W *ᵥ c) (wardF b E X' *ᵥ c') 1 1 +
              ((sigmaPlus b : ℝ) : ℂ) / W *
                (bilinear u 1 (nearSel W *ᵥ c') * bilinear (wardF b E X' *ᵥ c) 1 v))‖ ≤
          CJ * Cf ^ 4 * (covErr b E (b3Jet b E) (nearSchur (boundaryZ b E) X') +
            (jetDistance0 b E (nearSchur (boundaryZ b E) X') + (W : ℝ)⁻¹) ^ 2))
    (hJ1 : ∀ X' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X'.IsHermitian →
      conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) X')) ≤ max R 0 ^ 2 / 2 →
      ∀ (u v : Fin W → ℂ) (c c' : Fin 2 × Fin W → ℂ) (Cf : ℝ), vecNorm u ≤ Cf →
        vecNorm v ≤ Cf → vecNorm (nearSel W *ᵥ c) ≤ Cf → vecNorm (nearSel W *ᵥ c') ≤ Cf →
        vecNorm (passiveF b E (nearSchur (boundaryZ b E) X') *ᵥ (nearSel W *ᵥ c)) ≤ Cf →
        vecNorm (passiveF b E (nearSchur (boundaryZ b E) X') *ᵥ (nearSel W *ᵥ c')) ≤ Cf →
        ‖∫ F, bilinear u (freshDelta b E (nearSchur (boundaryZ b E) X') F) v *
              bilinear c (freshTransport b E X' F * nearProjection W *
                (freshTransport b E X' F)ᴴ - nearProjection W) c' ∂freshLaw W b -
            (sigmaMinus b E (b3Jet b E) / W * crossedTensor u v (nearSel W *ᵥ c)
                (passiveF b E (nearSchur (boundaryZ b E) X') *ᵥ (nearSel W *ᵥ c')) 1 1 +
              ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear u 1 (nearSel W *ᵥ c') *
                bilinear (passiveF b E (nearSchur (boundaryZ b E) X') *ᵥ (nearSel W *ᵥ c)) 1 v))‖
          ≤ CJ * Cf ^ 4 * ((W : ℝ)⁻¹ / Real.sqrt W +
            covErr b E (b3Jet b E) (nearSchur (boundaryZ b E) X') +
            (jetDistance0 b E (nearSchur (boundaryZ b E) X') + (W : ℝ)⁻¹) ^ 2))
    (hΔ : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∫⁻ f, ENNReal.ofReal (‖freshDelta b E X f‖ ^ 2) ∂freshLaw W b ≤ ENNReal.ofReal (C₂ ^ 2))
    (h4 : ∀ X' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X'.IsHermitian →
      ∫ y, ‖freshTransport b E X' y‖ ^ 4 ∂freshLaw W b ≤ C₄ ∧
        Integrable (fun y => ‖freshTransport b E X' y‖ ^ 4) (freshLaw W b))
    (ij : Fin np × Fin np) (g : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    CovLayerAt b3CovErr b3CovZ b E τ m s h R Vs j
      (2 * (CJ * ((1 + ‖cZero b E‖) * Real.sqrt R) ^ 4) +
        ‖sigmaMinus b E (b3Jet b E)‖ * ‖cZero b E‖ * Real.sqrt R ^ 2) 2
      (Sum.inr ij) (Sum.inl g) := by
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  have hsj : closeLen s W ≤ j := hj'.1.1
  obtain ⟨hXm, hXinv, hrel⟩ := hch
  have hη : 0 < etaZ b E := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hV := Modul.eq_of_growth hsj hVs
  have hVm : Measurable Vs :=
    hVs.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set r := Real.sqrt R with hrdef
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  set c0 := ‖cZero b E‖
  have hc0 : 0 ≤ c0 := norm_nonneg _
  set Cf := (1 + c0) * r
  set X' : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) →
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fun x => XX (b3Rebuild W j x)
  set U' : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) →
      Matrix (Fin 2 × Fin W) (SrcCol K (Fin np)) ℂ :=
    fun x => b3ClosedFrameAt b E s h τ m W j Vs (b3Rebuild W j x)
  set cu : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) → Fin W → ℂ :=
    fun x => clipVec r (closedNearU b E s h τ m W j ij.1 (b3Rebuild W j x))
  set cv : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) → Fin W → ℂ :=
    fun x => clipVec r (closedNearV b E s h τ m W j ij.2 (b3Rebuild W j x))
  have hX'm : Measurable X' := hXm.comp (measurable_b3Rebuild W j)
  have hU'm : Measurable U' :=
    (measurable_b3ClosedFrameAt b E s h τ m W j hVm).comp (measurable_b3Rebuild W j)
  have hcum : Measurable cu := measurable_clipVec_comp _
    ((measurable_closedNearU b E s h τ m j ij.1).comp (measurable_b3Rebuild W j))
  have hcvm : Measurable cv := measurable_clipVec_comp _
    ((measurable_closedNearV b E s h τ m j ij.2).comp (measurable_b3Rebuild W j))
  have hXy : ∀ y, X' (b3Past W j y) = XX y := fun y => by
    simp only [X', b3Rebuild_b3Past, hXinv]
  have hUy : ∀ y, U' (b3Past W j y) = b3ClosedFrameAt b E s h τ m W j Vs y := fun y => by
    simp only [U', b3Rebuild_b3Past]
    exact b3ClosedFrameAt_b3Ext b E s h τ m hsj le_rfl hV y
  have hcuy : ∀ y, cu (b3Past W j y) = clipVec r (closedNearU b E s h τ m W j ij.1 y) :=
    fun y => by simp only [cu, b3Rebuild_b3Past, closedNearU_b3Ext hsj le_rfl]
  have hcvy : ∀ y, cv (b3Past W j y) = clipVec r (closedNearV b E s h τ m W j ij.2 y) :=
    fun y => by simp only [cv, b3Rebuild_b3Past, closedNearV_b3Ext hsj le_rfl]
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j Vs
  have hA : A =ᵐ[μ] b3AliveM b E s h τ m R W j Vs :=
    b3Alive_ae_eq (by linarith) hE1 hE2 s h τ m R W j Vs
  have hAm : MeasurableSet[b3Sigma W j np] (b3AliveM b E s h τ m R W j Vs) :=
    Modul.measurableSet_b3AliveM_past (b := b) (E := E) s h τ m R hsj le_rfl hVs
  obtain ⟨A', hA'm, hA'⟩ := hAm
  set S : Set (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) :=
    A' ∩ {x | ((U' x)ᴴ * U' x).trace.re ≤ R} ∩ {x | (X' x).IsHermitian}
  have hSm : MeasurableSet S :=
    (hA'm.inter (measurableSet_le (measurable_trace_re_gram hU'm) measurable_const)).inter
      (measurableSet_isHermitian hX'm)
  set Q : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) → LayerSample W .oneBlockOnePort → ℂ :=
    fun x f => bilinear (cu x) (freshDelta b E (nearSchur (boundaryZ b E) (X' x)) f) (cv x) *
      incr b E (X' x) (U' x) g f
  have hQm : Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => Q z.1 z.2 := by
    have hΔm := BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E
      (BlockBand.SourceProcess.FullSource.measurable_nearSchur_comp (boundaryZ b E)
        (hX'm.comp measurable_fst)) measurable_snd
    have hm1 := (ClosedSummedProof.measurable_layerGramEntry b E (hX'm.comp measurable_fst)
      (hU'm.comp measurable_fst) measurable_snd g).sub
      (ClosedSummedProof.measurable_gramEntry_gramPair (hU'm.comp measurable_fst) g)
    exact (BlockBand.SourceProcess.RawTag.measurable_bilinear_jt (hcum.comp measurable_fst) hΔm
      (hcvm.comp measurable_fst)).mul hm1
  set Ψ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ :=
    (S ×ˢ Set.univ).indicator fun z => Q z.1 z.2
  have hΨm : Measurable Ψ := hQm.indicator (hSm.prod MeasurableSet.univ)
  have hΨ1 : ∀ x f, x ∈ S → Ψ (x, f) = Q x f := fun x f hx =>
    Set.indicator_of_mem (Set.mk_mem_prod hx (Set.mem_univ f)) _
  have hΨ0 : ∀ x f, x ∉ S → Ψ (x, f) = 0 := fun x f hx =>
    Set.indicator_of_notMem (fun hh => hx (Set.mem_prod.mp hh).1) _
  have hpast : ∀ᵐ y ∂μ, y ∈ A → b3Past W j y ∈ S := by
    filter_upwards [hrel, hA] with y hy hyA hyAl
    have hyM : y ∈ b3AliveM b E s h τ m R W j Vs := (Iff.of_eq hyA).mp hyAl
    refine ⟨⟨by rw [← hA'] at hyM; exact hyM, ?_⟩, ?_⟩
    · show ((U' (b3Past W j y))ᴴ * U' (b3Past W j y)).trace.re ≤ R
      rw [hUy]
      exact (hyAl.2 j hsj le_rfl).le
    · show (X' (b3Past W j y)).IsHermitian
      rw [hXy]
      exact (hy hyAl).1
  -- the frames are bounded by `r` on the alive set
  have hnorm : ∀ᵐ y ∂μ, y ∈ A → vecNorm (closedNearU b E s h τ m W j ij.1 y) ≤ r ∧
      vecNorm (closedNearV b E s h τ m W j ij.2 y) ≤ r := by
    filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW1,
      ae_closedPhase_good (W := W) (np := np) b E s h j] with y hP hQ hyA
    have htr := hyA.2 j hsj le_rfl
    exact ⟨norm_closedNearU_le b E s h τ m j Vs ij.1 y htr,
      norm_closedNearV_le b E s h hh τ m j Vs ij.2 y (hP.2.2.2 j) (isUnit_iff_ne_zero.2 hQ.1) htr⟩
  have heq : A.indicator (fun y => b3dX b E s h τ m W j Vs (Sum.inr ij) y *
      b3dX b E s h τ m W j Vs (Sum.inl g) y) =ᵐ[μ]
      fun y => Ψ (b3Past W j y, freshSample W j y.1.1) := by
    filter_upwards [hrel, hA, hpast, indicator_kdX_ae hb0 hb hE1 hE2 s h hh τ m hW1 Vs R hj1 hj ij,
      hnorm] with y hy hyA hyp hk hn
    by_cases hyAl : y ∈ A
    · have hyM : y ∈ b3AliveM b E s h τ m R W j Vs := (Iff.of_eq hyA).mp hyAl
      rw [Set.indicator_of_mem hyAl, hΨ1 _ _ (hyp hyAl)]
      rw [Set.indicator_of_mem hyAl, Set.indicator_of_mem hyM] at hk
      obtain ⟨-, hN, hfr, -, -⟩ := hy hyAl
      rw [hk]
      simp only [Q, hXy, hUy, hcuy, hcvy, clipVec_of_le (hn hyAl).1, clipVec_of_le (hn hyAl).2, hN]
      congr 1
      simp only [incr, layerGram, b3dX, b3X, cEntry, b3ClosedGramAt, hfr]
      rfl
    · have hyM : y ∉ b3AliveM b E s h τ m R W j Vs := fun hh => hyAl ((Iff.of_eq hyA).mpr hh)
      have hx : b3Past W j y ∉ S := fun hx => hyM (by rw [← hA']; exact hx.1.1)
      rw [Set.indicator_of_notMem hyAl, hΨ0 _ _ hx]
  have hint : Integrable (fun y => Ψ (b3Past W j y, freshSample W j y.1.1)) μ := by
    refine integrable_closed_of_fresh_b3 b j hΨm
      ((r ^ 4 * C₂ ^ 2) + 2 * max R 0 ^ 2 * (C₄ + 1)) fun x => ?_
    by_cases hx : x ∈ S
    · simp only [hΨ1 x _ hx]
      have hXp : (passiveY (nearSchur (boundaryZ b E) (X' x))).PosSemidef :=
        BlockBand.SourceProcess.FullSource.nearSchur_passive hη hx.2
      refine (lintegral_dK_incr_le (vecNorm_clipVec_le hr _) (vecNorm_clipVec_le hr _)
        (hΔ _ hXp) (h4 (X' x) hx.2).1 (h4 (X' x) hx.2).2 (U' x) (le_max_right R 0)
        (hx.1.2.trans (le_max_left R 0)) g).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    · simp only [hΨ0 x _ hx, enorm_zero, lintegral_const, zero_mul]
      exact zero_le
  have hce := (condExp_congr_ae (m := b3Sigma W j np) heq).trans
    (condExp_closed_fresh b j hΨm hint)
  unfold CovLayerAt
  filter_upwards [hce, hrel, hpast, hnear, hnorm,
    ae_closedNearV_eq_closedPS hb0 hb hE1 hE2 s h hh τ m hW1 j Vs,
    ae_passive_b3ClosedX (np := np) hb0 hb hE1 hE2 s h hh τ m hW1 j] with y hy hyr hyp hny hn
    hv hpy hyAl
  rw [hy]
  obtain ⟨hH, hN, -, hcur, -⟩ := hyr hyAl
  have hxin := hyp hyAl
  set x := b3Past W j y
  have hint_eq : ∫ f, Ψ (x, f) ∂freshLaw W b = ∫ f, Q x f ∂freshLaw W b :=
    integral_congr_ae (Eventually.of_forall fun f => hΨ1 x f hxin)
  rw [hint_eq]
  set u := closedNearU b E s h τ m W j ij.1 y with hudef
  set v := closedNearV b E s h τ m W j ij.2 y with hvdef
  set V := b3ClosedFrameAt b E s h τ m W j Vs y with hVdef
  set XY := XX y with hXYdef
  have hu : vecNorm u ≤ r := (hn hyAl).1
  have hvn : vecNorm v ≤ r := (hn hyAl).2
  have htr : (Vᴴ * V).trace.re < R := hyAl.2 j hsj le_rfl
  have hQx : ∀ f, Q x f = bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XY) f) v *
      incr b E XY V g f := fun f => by
    simp only [Q, x, hXy, hUy, hcuy, hcvy, clipVec_of_le hu, clipVec_of_le hvn, u, v, V, XY]
  rw [integral_congr_ae (Eventually.of_forall hQx)]
  have hu_eq : u = nearSel W *ᵥ fun a => V a (Sum.inr ij.1) :=
    closedNearU_eq_nearSel b E s h τ m W j Vs ij.1 y
  have hcolS : ∀ d, nearSel W *ᵥ (twoPortScattering b E XY *ᵥ fun a => V a d) =
      nearSel W *ᵥ (b3ClosedPS b E s h W j y.1.1 (phase y.2) *ᵥ fun a => V a d) := fun d => by
    rw [mulVec_mulVec, mulVec_mulVec, ← col_mul_eq, ← col_mul_eq, hny hyAl]
  have hvPS : v = nearSel W *ᵥ (b3ClosedPS b E s h W j y.1.1 (phase y.2) *ᵥ
      fun a => V a (Sum.inr ij.2)) := hv ij.2
  have hv_eq : v = nearSel W *ᵥ (twoPortScattering b E XY *ᵥ fun a => V a (Sum.inr ij.2)) := by
    rw [hcolS]; exact hvPS
  have hQZ : ∀ k, ‖bilinear (nearSel W *ᵥ fun a => V a k) 1 v‖ ≤
      ‖b3CovZ b E np τ m s h K W Vs j y‖ := fun k => by
    rw [norm_b3CovZ]
    have e1 : bilinear (nearSel W *ᵥ fun a => V a k) 1 v =
        b3ContrCoord b E s h τ m W j Vs 0 k (Sum.inr ij.2) y := by
      rw [hvPS, bilinear_one, dot_nearSel, mulVec_mulVec, nearPortProj_mul_b3ClosedPS,
        b3ContrCoord, entry_eq_dot]
      rfl
    rw [e1]
    exact norm_b3ContrCoord_le_b3CovZ b E np τ m s h K W Vs j 0 k (Sum.inr ij.2) y
  obtain ⟨hWe, hδ, hcov⟩ := layerErrX_facts hb hκ hE hW1 hpy
  set e := b3LayerErrX b E (b3ClosedX b E s h τ m W j y) with hedef
  have hδ' : (jetDistance0 b E (nearSchur (boundaryZ b E) XY) + (W : ℝ)⁻¹) ^ 2 ≤ e ^ 2 := by
    rw [hN]; exact hδ
  have hcov' : covErr b E (b3Jet b E) (nearSchur (boundaryZ b E) XY) ≤
      (W : ℝ)⁻¹ / Real.sqrt W + e ^ 2 := by
    rw [hN]; exact hcov
  have hcc : cCov b E (Sum.inr ij : CIdx K np) (Sum.inl g)
      (b3ClosedGramAt b E s h τ m W j Vs y) = kGramCov b E ij g (Vᴴ * V, Vᴴ * nearPortProj W * V) :=
    rfl
  rw [hcc]
  have hg : conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XY)) ≤
      max R 0 ^ 2 / 2 := by
    refine (cond_le_of_current hb hκ hE hH V hcur).trans ?_
    have h0 := trace_re_gram_nonneg V
    have := pow_le_pow_left₀ h0 (htr.le.trans (le_max_left R 0)) 2
    linarith
  exact mixed_eval hb0 hE1 hE2 hη hW1 XY hH V hcur u v ij hr hu hvn
    (fun d => vecNorm_col_le V d htr)
    hu_eq hv_eq (hJ0 XY hH) (hJ1 XY hH hg) hCJ hWe hδ' hcov' (norm_nonneg _) hQZ g

/-! ## `CovLayerHypKG` -/

/-- **`CovLayerHypKG b3CovErr b3CovZ`** (the mixed `(𝒦, Gram)` pairs of `CovLayerHyp`) from the
Gaussian inputs, the cubic fresh bound `FreshDeltaQuadCov` and the near-rows chain hypothesis. -/
theorem covLayerHypKG_of_near (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hQ : ClosedForm.FreshDeltaQuadCov) (hN : B3ClosedChainNearPin) :
    CovLayerHypKG b3CovErr b3CovZ := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  have hh : h ^ 2 < 1 := by nlinarith [hFD.2.2.2.1, hFD.2.2.2.2.1]
  have hjet := b3Jet_spec hb0 hb hE1 hE2
  obtain ⟨C0, W0, hC0, hJ0⟩ := ClosedForm.fresh_dK_dM_le hGA hLp hP hb0 hb hκ
  obtain ⟨C1, W1, hC1, hJ1⟩ := ClosedForm.fresh_dK_dB_le hGA hLp hP hQ hb0 hb hκ
  obtain ⟨C₂, W₂, hC₂0, hM⟩ := fresh_delta_memLp hGA hb0 hb hκ
  obtain ⟨C₄, W₄, hC₄, h4⟩ := ClosedSummedProof.fresh_pow_bound hGA hb0 hb hκ
  obtain ⟨Cch, -, hevC⟩ := hN b E np τ m T s h K Vs hFD R
  set CJ := max C0 C1
  have hCJ : 0 ≤ CJ := le_max_of_le_left hC0
  refine ⟨2 * (CJ * ((1 + ‖cZero b E‖) * Real.sqrt R) ^ 4) +
    ‖sigmaMinus b E (b3Jet b E)‖ * ‖cZero b E‖ * Real.sqrt R ^ 2, 2, by positivity, le_rfl, ?_⟩
  filter_upwards [hevC, hFD.2.2.2.2.2, eventually_ge_atTop 1, eventually_ge_atTop W0,
    eventually_ge_atTop W1, eventually_ge_atTop W₂, eventually_ge_atTop W₄,
    B3Cur.eventually_one_le_closeLen hFD.2.1] with W hW hVW hW1 hW0' hW1' hW2 hW4 hs1 j hj ij g
  obtain ⟨XX, hch, hnear⟩ := hW j hj
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  have hjs : 1 ≤ j := hs1.trans hj'.1.1
  have hη : 0 < etaZ b E := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hpos : ∀ X' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X'.IsHermitian →
      0 ≤ covErr b E (b3Jet b E) (nearSchur (boundaryZ b E) X') +
        (jetDistance0 b E (nearSchur (boundaryZ b E) X') + (W : ℝ)⁻¹) ^ 2 := fun X' hX' =>
    add_nonneg (covErr_nonneg hb hκ hE _
      (BlockBand.SourceProcess.FullSource.nearSchur_passive hη hX')) (sq_nonneg _)
  have hΔ : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∫⁻ f, ENNReal.ofReal (‖freshDelta b E X f‖ ^ 2) ∂freshLaw W b ≤
        ENNReal.ofReal (C₂ ^ 2) := fun X hX =>
    lintegral_sq_le_of_eLpNorm _ (fun _ => norm_nonneg _) hC₂0
      (by rw [ENNReal.ofReal_ofNat]; exact (hM W hW2 E hE X hX).2.1)
  have hA := covLayerAt_mixed_step hb0 hb hE1 hE2 hκ hE s h hh τ m R hW1 hjs hj hVW.1 hch hnear
    hCJ hC₄
    (fun X' hX' u v c c' Cf h1 h2 h3 h4' h5 h6 =>
      (hJ0 W hW0' E hE (b3Jet b E) hjet X' hX' u v c c' Cf h1 h2 h3 h4' h5 h6).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (by have := (Transmission.PassiveCovariance.vecNorm_nonneg u).trans h1; positivity))
          (hpos X' hX')))
    (fun X' hX' _ u v c c' Cf h1 h2 h3 h4' h5 h6 =>
      (hJ1 W hW1' E hE (b3Jet b E) hjet X' hX' u v c c' Cf h1 h2 h3 h4' h5 h6).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (by have := (Transmission.PassiveCovariance.vecNorm_nonneg u).trans h1; positivity))
          (by linarith [hpos X' hX', (by positivity : (0 : ℝ) ≤ (W : ℝ)⁻¹ / Real.sqrt W)])))
    hΔ (fun X' hX' => h4 W hW4 E hE X' hX') ij g
  refine ⟨hA, ?_⟩
  unfold CovLayerAt at hA ⊢
  have hf : (fun y => b3dX b E s h τ m W j (Vs W) (Sum.inl g) y *
      b3dX b E s h τ m W j (Vs W) (Sum.inr ij) y) =
      fun y => b3dX b E s h τ m W j (Vs W) (Sum.inr ij) y *
        b3dX b E s h τ m W j (Vs W) (Sum.inl g) y := funext fun y => mul_comm _ _
  rw [hf]
  exact hA

end BlockBand.SourceProcess.PhysApprox.B3

