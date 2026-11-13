module

public import BlockBand.Layers.FullEnergyCore
public import BlockBand.Layers.FullEnergyStep

/-!
# `FetPathBound`: the path recursion of the energy derivative

The path sentence of the energy paragraph in the proof of the tagged-trace lemma: the
contraction gives outgoing error `q_*|f' - a'| + Cδ(1+s_r) + C(1+s_r)/W` and noise
`C_p(1+s_r)/√W`, and the full clock bound proves `‖f'_r - a'‖_{L^p} ≤ C_p(r+1)/√W`, with exits
removed as in the clock-moments lemma (`fetPathBound_holds (hcount) (hgrad) : FetPathBound`).

Law: `pathLaw W r b`, `1 ≤ r ≤ TW`; `z = z_∂(E)`, `E ∈ bulkInterval κ`; `X_r = pathSchur E ω`,
`X_r' = fetXd E ω`, `D_r = fetPathDist b E ω = max_i |f'_{r,i} - a'|`, `s_r = fetClock(X_r, X_r')`
(the full energy clock), `δ_r = matchedDistance b E X_r`, `a_r = ‖D_r‖_{L^p(pathLaw W r b)}`.

## Proof

1. **Outgoing derivative** (`fetR_fd_grow_eq`, deterministic): along the two-ended growth
   `pathLaw (r+2) = (pathLaw r ⊗ layerLaw) ∘ (pgGrow ∘ swap)⁻¹` (`measurePreserving_pgGrow`), the
   path derivative of the grown path is the outgoing layer derivative,
   `f'_{r+2,j} = ġ_j = fetGd(X_r, X_r', ℓ)_j`: both are energy derivatives of the same port trace
   (`pathPortResolvent_pgGrow` near `E`, `fetC_hasDerivAt_pathTrace`, and the a.s. derivative of the
   energy clause of the differentiated-covariance lemma, `tgtEnergyClause`).
2. **Conditional step** (on `δ_r ≤ d_*`): `FetStepMean` (`|E ġ_j - a'| ≤ q d + C(1+u)(δ+1/W)`,
   `q < 1`) and the noise clause (`‖ġ_j - E ġ_j‖_p ≤ C_p(1+u)/√W`, `tgtNoiseClause`) give
   `‖D_{r+2}‖_{L^p(layer)} ≤ q D_r + C'(1+s_r)(δ_r + W^{-1/2})`.
3. **Exit removal** (the paper's "exits are removed"): off `δ_r ≤ d_*` the weight `δ_r/d_* ≥ 1`
   is used instead of the stopping indicator, with the crude deterministic bound
   `D ≤ s + C₀` (`fetR_dist_le`, trace pairing with the clock) and Hölder:
   `‖1_{δ_r > d_*} D_{r+2}‖_p ≤ d_*⁻¹ ‖δ_r‖_{2p} ‖D_{r+2}‖_{2p}`; the scalar moments
   `‖δ_r‖_{2p} ≤ C/W` are the matched-traces theorem (path clause).
4. **Recursion** (`fetR_step`, `fetR_arith`): with the full clock moments
   `‖s_r‖_{2p} ≤ C(r+1)` (`clockMoments_holds`), `a_{r+2} ≤ q a_r + B(r+1)/√W`; from the cores
   `a_{1,2} ≤ C/√W` (`FetCoreBound`), strong induction gives `a_r ≤ A(r+1)/√W`,
   `A = C_core + B/(1-q)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Deterministic facts along the path
-/

section Det

variable {W r : ℕ}

/-- `(H - E)⁻¹` is Hermitian for a path with Hermitian blocks. -/
theorem fetR_inv_isHermitian {ω : PathSample W r} (hA : ∀ j, (ω.1 j).IsHermitian) (E : ℝ) :
    ((pathMatrix ω - (E : ℂ) • 1)⁻¹).IsHermitian := by
  have hH : (pathMatrix ω - (E : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)).IsHermitian := by
    refine (srec_pathMatrix_isHermitian ω hA).sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  exact hH.inv

/-- `X_r' = B_p*(H - E)⁻²B_p ⪰ 0`. -/
theorem fetR_xd_posSemidef {ω : PathSample W r} (hA : ∀ j, (ω.1 j).IsHermitian) (E : ℝ) :
    (fetXd E ω).PosSemidef := by
  have hN := fetR_inv_isHermitian hA E
  have e : fetXd E ω = ((pathMatrix ω - (E : ℂ) • 1)⁻¹ * pathPortCoupling ω)ᴴ *
      ((pathMatrix ω - (E : ℂ) • 1)⁻¹ * pathPortCoupling ω) := by
    rw [conjTranspose_mul, hN.eq]
    simp only [fetXd, Matrix.mul_assoc]
  rw [e]
  exact posSemidef_conjTranspose_mul_self _

/-- The full energy clock `s_r = W⁻¹ Re Tr R_r* X_r' R_r` is the clock of the clock-moments lemma
(`clkCoreSource` with the full tag). -/
theorem fetR_clock_eq {b E : ℝ} {ω : PathSample W r} (hA : ∀ j, (ω.1 j).IsHermitian) :
    fetClock b E (pathSchur E ω) (fetXd E ω) =
      clkTrace (clkCoreSource b E (fun _ => true) ω) := by
  rw [clkCoreSource_eq_source b E _ ω (srec_pathMatrix_isHermitian ω hA), clkProj_true]
  unfold fetClock fetR fetXd pathPortResolvent
  simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- **Crude bound** (deterministic): `max_i |f'_i - a'| ≤ u + Z η⁻² + A` for Hermitian `X`,
`S ⪰ 0`, `Im z_∂ ≥ η`, `|z_∂'| ≤ Z`, `|a'| ≤ A` (trace pairing of `S = K*YK` with the clock
`Y = R*SR`, `‖KR‖ = 1`, `‖RK*‖ ≤ 1`). -/
theorem fetR_dist_le {b E η Z A : ℝ} {X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (hS : S.PosSemidef) (hη : 0 < η) (hz : η ≤ (boundaryZ b E).im)
    (hZ : ‖tgtZd b E‖ ≤ Z) (hA : ‖tgtAd E‖ ≤ A) :
    fetDist b E X S ≤ fetClock b E X S + (Z * (η⁻¹) ^ 2 + A) := by
  have hz0 : 0 < (boundaryZ b E).im := hη.trans_le hz
  set K := boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X with hKdef
  set R := fetR b E X with hRdef
  have hRK : R = K⁻¹ := rfl
  have hdet : IsUnit K.det := isUnit_iff_ne_zero.mpr (resolvent_det_ne_zero X hX _ hz0)
  set Y := Rᴴ * S * R with hY
  have hYpsd : Y.PosSemidef := hS.conjTranspose_mul_mul_same R
  have hSY : S = Kᴴ * Y * K := by
    have h1 : R * K = 1 := by rw [hRK]; exact nonsing_inv_mul K hdet
    calc S = (R * K)ᴴ * S * (R * K) := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = Kᴴ * Y * K := by rw [conjTranspose_mul]; simp only [hY, Matrix.mul_assoc]
  have hu : fetClock b E X S = (W : ℝ)⁻¹ * Y.trace.re := rfl
  have hu0 : 0 ≤ fetClock b E X S := clkTrace_nonneg hYpsd
  have hRn : ‖R‖ ≤ η⁻¹ := (fetS_norm_R_le hX hz0).trans (inv_anti₀ hη hz)
  have hKR : ‖K * R‖ ≤ 1 := by
    rw [hRK, mul_nonsing_inv K hdet]; exact lct_norm_one_le
  have hRKs : ‖R * Kᴴ‖ ≤ 1 := fetS_norm_RK_le hX hz0
  have hη0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hi : ∀ i : Fin 2, ‖fetFd b E X S i - tgtAd E‖ ≤ fetClock b E X S + (Z * (η⁻¹) ^ 2 + A) := by
    intro i
    have e : fetFd b E X S i = blockTrace (R * (Kᴴ * Y * K) * R) i -
        tgtZd b E * blockTrace (R * R) i := by
      unfold fetFd
      rw [← hRdef, Matrix.mul_sub, Matrix.sub_mul, fetS_blockTrace_sub, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, fetS_blockTrace_smul, ← hSY]
    have h1 := fetS_pair_le hYpsd K R R i
    have h1' : ‖blockTrace (R * (Kᴴ * Y * K) * R) i‖ ≤ fetClock b E X S := by
      rw [hu]
      have hy0 : 0 ≤ (W : ℝ)⁻¹ * Y.trace.re := by rw [← hu]; exact hu0
      calc _ ≤ ‖K * R‖ * ‖R * Kᴴ‖ * ((W : ℝ)⁻¹ * Y.trace.re) := h1
        _ ≤ 1 * 1 * ((W : ℝ)⁻¹ * Y.trace.re) := by gcongr
        _ = _ := by ring
    have h2 : ‖blockTrace (R * R) i‖ ≤ (η⁻¹) ^ 2 := by
      refine (lct_norm_blockTrace_le _ i).trans ((norm_mul_le _ _).trans ?_)
      rw [sq]
      exact mul_le_mul hRn hRn (norm_nonneg _) hη0
    have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
    rw [e]
    calc ‖blockTrace (R * (Kᴴ * Y * K) * R) i - tgtZd b E * blockTrace (R * R) i - tgtAd E‖
        ≤ ‖blockTrace (R * (Kᴴ * Y * K) * R) i‖ + ‖tgtZd b E‖ * ‖blockTrace (R * R) i‖ +
            ‖tgtAd E‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) le_rfl)
          rw [norm_mul]
      _ ≤ fetClock b E X S + Z * (η⁻¹) ^ 2 + A := by
          gcongr
      _ = _ := by ring
  exact max_le (hi 0) (hi 1)

/-- **The outgoing derivative is the path derivative of the grown path** (deterministic): if
`H - E` and the grown `H' - E` are invertible, `z_∂ - X_{r+2}` is invertible, and the outgoing
port trace `E' ↦ W⁻¹ Tr Q_j 𝒢(E')` of the layer (old input `X_r(E')`) has derivative `ġ_j` at
`E`, then `f'_{r+2,j} = ġ_j`. -/
theorem fetR_fd_grow_eq {b E : ℝ} (hr : 1 ≤ r) (hE : E ∈ Set.Ioo (-2 : ℝ) 2)
    (ℓ : LayerSample W .separate) (ω : PathSample W r)
    (hH : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hG : IsUnit (pathMatrix (pgGrow (ℓ, ω)) - (E : ℂ) • 1).det)
    (hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      pathSchur E (pgGrow (ℓ, ω))).det) (j : Fin 2)
    (hd : HasDerivAt (fun E' : ℝ => (W : ℂ)⁻¹ * (meqPortProj (W := W) (σ := .separate) j *
        layerResolvent .separate E' (boundaryZ b E') (pathSchur E' ω) ℓ).trace)
      (fetGd b E (pathSchur E ω) (fetXd E ω) ℓ j) E) :
    fetFd b E (pathSchur E (pgGrow (ℓ, ω))) (fetXd E (pgGrow (ℓ, ω))) j =
      fetGd b E (pathSchur E ω) (fetXd E ω) ℓ j := by
  have h1 := fetC_hasDerivAt_pathTrace b hE (pgGrow (ℓ, ω)) hG hK j
  have heq : (fun E' : ℝ => blockTrace (pathPortResolvent b E' (pgGrow (ℓ, ω))) j) =ᶠ[𝓝 E]
      (fun E' : ℝ => (W : ℂ)⁻¹ * (meqPortProj (W := W) (σ := .separate) j *
        layerResolvent .separate E' (boundaryZ b E') (pathSchur E' ω) ℓ).trace) := by
    filter_upwards [fetC_eventually_unit E ω hH, fetC_eventually_unit E (pgGrow (ℓ, ω)) hG]
      with E' h1' h2'
    have hS := (isUnit_det_pgGrow_iff hr E' ℓ ω h1').mp h2'
    rw [pathPortResolvent_pgGrow hr b E' ℓ ω h1' hS, ← lct_port_eq_trace]
    rfl
  exact h1.unique (hd.congr_of_eventuallyEq heq)

end Det

/-!
## 2. Measurability and `L^p` helpers
-/

section Helpers

variable {W r : ℕ}

theorem fetR_isProb_path (W r : ℕ) (b : ℝ) : IsProbabilityMeasure (pathLaw W r b) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  unfold pathLaw; infer_instance

/-- `pathLaw`-a.s. the blocks are Hermitian. -/
theorem fetR_ae_blocks (W r : ℕ) (b : ℝ) : ∀ᵐ ω ∂pathLaw W r b, ∀ j, (ω.1 j).IsHermitian := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have h := ae_blocks_isHermitian r W (Real.toNNReal ((1 - 2 * b) / W))
  unfold pathLaw
  exact (Measure.quasiMeasurePreserving_fst).ae h

theorem fetR_measurable_xd (E : ℝ) : Measurable (fun ω : PathSample W r => fetXd E ω) := by
  have hD : Measurable (fun ω : PathSample W r => (pathMatrix ω - (E : ℂ) • 1)⁻¹) :=
    measurable_matrix_inv.comp ((measurable_pathMatrix W r).sub measurable_const)
  have hB := measurable_pathPortCoupling W r
  exact srec_measurable_mul (srec_measurable_mul (srec_measurable_mul
    (srec_measurable_conjTranspose hB) hD) hD) hB

theorem fetR_measurable_clock (b E : ℝ) :
    Measurable (fun ω : PathSample W r => fetClock b E (pathSchur E ω) (fetXd E ω)) := by
  have hR : Measurable (fun ω : PathSample W r => fetR b E (pathSchur E ω)) :=
    measurable_matrix_inv.comp (measurable_const.sub (measurable_pathSchur W r E))
  exact clk_measurable_trace (srec_measurable_mul (srec_measurable_mul
    (srec_measurable_conjTranspose hR) (fetR_measurable_xd E)) hR)

theorem fetR_measurable_dist (b E : ℝ) :
    Measurable (fun ω : PathSample W r => matchedDistance b E (pathSchur E ω)) :=
  (srec_measurable_matchedDistance b E W).comp (measurable_pathSchur W r E)

theorem fetR_measurable_gd (b E : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (j : Fin 2) : Measurable (fun ℓ : LayerSample W .separate => fetGd b E X S ℓ j) := by
  have hG := measurable_layerResolvent .separate E (boundaryZ b E) X
  have hc : Continuous (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
      -((W : ℂ)⁻¹ * (meqPortProj (W := W) (σ := .separate) j * (M * fetP b E S * M)).trace)) :=
    (continuous_const.mul (Continuous.matrix_trace (continuous_const.matrix_mul
      ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id)))).neg
  exact hc.measurable.comp hG

theorem fetR_eLpNorm_smul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (q : ℝ≥0∞) :
    eLpNorm (fun x => c * f x) q μ = ENNReal.ofReal c * eLpNorm f q μ := by
  have e : (fun x => c * f x) = c • f := rfl
  rw [e, eLpNorm_const_smul, Real.enorm_of_nonneg hc]

theorem fetR_eLpNorm_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {c : ℝ} (hc : 0 ≤ c) {q : ℝ} (hq : 0 < q) :
    eLpNorm (fun _ : Ω => c) (ENNReal.ofReal q) μ = ENNReal.ofReal c := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  rw [eLpNorm_const _ hq0 (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow, mul_one,
    Real.enorm_of_nonneg hc]

theorem fetR_eLpNorm_one_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (fun x => 1 + f x) (ENNReal.ofReal q) μ ≤ 1 + eLpNorm f (ENNReal.ofReal q) μ := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr hq
  refine (eLpNorm_add_le (f := fun _ => (1 : ℝ)) (g := f) hq1).trans ?_
  rw [fetR_eLpNorm_const zero_le_one (by linarith), ENNReal.ofReal_one]

end Helpers

/-!
## 3. One growth step
-/

section Step

variable {W r : ℕ}

/-- **Conditional step**: given an old path `ω` with Hermitian blocks,
`H - E` invertible and `δ_r ≤ d_*`, under the fresh layer
`‖D_{r+2}‖_{L^p(layer)} ≤ q D_r + C'(1 + s_r)δ_r + C' w (1 + s_r)`, `C' = C_s + 2C_p`,
from the step mean (`hmean`), the noise (`hnoise`) and the derivative identity
`f'_{r+2,j} = ġ_j` (`fetR_fd_grow_eq`, a.s. in the layer). -/
theorem fetR_cond {b E p q Cs Cp dstar w : ℝ} (hr : 1 ≤ r) (hE : E ∈ Set.Ioo (-2 : ℝ) 2)
    (hp : 1 ≤ p) (hCs : 0 ≤ Cs) (hCp : 0 ≤ Cp) (hw1 : 1 / (W : ℝ) ≤ w)
    (hw2 : 1 / Real.sqrt W ≤ w) (hz : 0 < (boundaryZ b E).im)
    (hmean : ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      matchedDistance b E X ≤ dstar → ∀ j : Fin 2,
        ‖(∫ ℓ, fetGd b E X S ℓ j ∂layerLaw W b .separate) - tgtAd E‖ ≤
          q * fetDist b E X S + Cs * (1 + fetClock b E X S) * (matchedDistance b E X + 1 / W))
    (hnoise : ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      ∀ j : Fin 2, eLpNorm (fun ℓ => fetGd b E X S ℓ j -
          ∫ ℓ', fetGd b E X S ℓ' j ∂layerLaw W b .separate) (ENNReal.ofReal p)
          (layerLaw W b .separate) ≤ ENNReal.ofReal (Cp * (1 + fetClock b E X S) / Real.sqrt W))
    (ω : PathSample W r) (hA : ∀ j, (ω.1 j).IsHermitian)
    (hH : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hgood : matchedDistance b E (pathSchur E ω) ≤ dstar)
    (hℓ : ∀ᵐ ℓ ∂layerLaw W b .separate, IsUnit (pathMatrix (pgGrow (ℓ, ω)) - (E : ℂ) • 1).det ∧
      (pathSchur E (pgGrow (ℓ, ω))).IsHermitian)
    (hdω : ∀ j : Fin 2, ∀ᵐ ℓ ∂layerLaw W b .separate, HasDerivAt (fun E' : ℝ => (W : ℂ)⁻¹ *
          (meqPortProj (W := W) (σ := .separate) j *
            layerResolvent .separate E' (boundaryZ b E') (pathSchur E' ω) ℓ).trace)
          (fetGd b E (pathSchur E ω) (fetXd E ω) ℓ j) E) :
    eLpNorm (fun ℓ => fetPathDist b E (pgGrow (ℓ, ω))) (ENNReal.ofReal p) (layerLaw W b .separate) ≤
      ENNReal.ofReal (q * fetPathDist b E ω +
        (Cs + 2 * Cp) * ((1 + fetClock b E (pathSchur E ω) (fetXd E ω)) *
          matchedDistance b E (pathSchur E ω)) +
        ((Cs + 2 * Cp) * w) * (1 + fetClock b E (pathSchur E ω) (fetXd E ω))) := by
  have hpl := bond_isProbabilityMeasure_layerLaw W b .separate
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  set ν := layerLaw W b .separate with hν
  set X := pathSchur E ω with hXdef
  set S := fetXd E ω with hSdef
  have hX : X.IsHermitian := srec_pathSchur_isHermitian E ω hA
  have hS : S.PosSemidef := fetR_xd_posSemidef hA E
  set u := fetClock b E X S with hu
  set δ := matchedDistance b E X with hδ
  have hu0 : 0 ≤ u := clkTrace_nonneg (hS.conjTranspose_mul_mul_same _)
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (le_max_left _ _)
  set m : Fin 2 → ℂ := fun j => ∫ ℓ, fetGd b E X S ℓ j ∂ν with hm
  set M := max ‖m 0 - tgtAd E‖ ‖m 1 - tgtAd E‖ with hM
  set n : Fin 2 → LayerSample W .separate → ℝ := fun j ℓ => ‖fetGd b E X S ℓ j - m j‖ with hn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (le_max_left _ _)
  have hae : ∀ᵐ ℓ ∂ν, ‖fetPathDist b E (pgGrow (ℓ, ω))‖ ≤ M + (n 0 ℓ + n 1 ℓ) := by
    filter_upwards [hℓ, hdω 0, hdω 1] with ℓ hℓ' h0 h1
    obtain ⟨hG, hherm⟩ := hℓ'
    have hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        pathSchur E (pgGrow (ℓ, ω))).det :=
      isUnit_iff_ne_zero.mpr (resolvent_det_ne_zero _ hherm _ hz)
    have e0 := fetR_fd_grow_eq hr hE ℓ ω hH hG hK 0 h0
    have e1 := fetR_fd_grow_eq hr hE ℓ ω hH hG hK 1 h1
    have hD0 : 0 ≤ fetPathDist b E (pgGrow (ℓ, ω)) := (norm_nonneg _).trans (le_max_left _ _)
    rw [Real.norm_of_nonneg hD0]
    unfold fetPathDist fetDist
    rw [e0, e1]
    have hj : ∀ j : Fin 2, ‖fetGd b E X S ℓ j - tgtAd E‖ ≤ M + (n 0 ℓ + n 1 ℓ) := by
      intro j
      have h1 := norm_sub_le_norm_sub_add_norm_sub (fetGd b E X S ℓ j) (m j) (tgtAd E)
      have hMj : ‖m j - tgtAd E‖ ≤ M := by
        fin_cases j
        · exact le_max_left _ _
        · exact le_max_right _ _
      have hnj : n j ℓ ≤ n 0 ℓ + n 1 ℓ := by
        have h0' : 0 ≤ n 0 ℓ := norm_nonneg _
        have h1' : 0 ≤ n 1 ℓ := norm_nonneg _
        fin_cases j
        · simp only [Fin.zero_eta]; linarith
        · simp only [Fin.mk_one]; linarith
      have : ‖fetGd b E X S ℓ j - m j‖ = n j ℓ := rfl
      linarith
    exact max_le (hj 0) (hj 1)
  have hnm : ∀ j : Fin 2, AEStronglyMeasurable (n j) ν := fun j =>
    ((fetR_measurable_gd b E X S j).sub measurable_const).norm.aestronglyMeasurable
  have hDm : AEStronglyMeasurable (fun ℓ => fetPathDist b E (pgGrow (ℓ, ω))) ν :=
    ((fetC_measurable_pathDist b E).comp ((measurePreserving_pgGrow (W := W) b hr).measurable.comp
      (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hn_le : ∀ j : Fin 2, eLpNorm (n j) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (Cp * (1 + u) / Real.sqrt W) := fun j => by
    have e : eLpNorm (n j) (ENNReal.ofReal p) ν =
        eLpNorm (fun ℓ => fetGd b E X S ℓ j - m j) (ENNReal.ofReal p) ν :=
      eLpNorm_norm _ ((fetR_measurable_gd b E X S j).sub measurable_const).aestronglyMeasurable
    rw [e]; exact hnoise X S hX hS j
  have hMle : M ≤ q * fetDist b E X S + Cs * (1 + u) * (δ + 1 / W) :=
    max_le (hmean X S hX hS hgood 0) (hmean X S hX hS hgood 1)
  have hN0 : 0 ≤ Cp * (1 + u) / Real.sqrt W := by positivity
  calc eLpNorm (fun ℓ => fetPathDist b E (pgGrow (ℓ, ω))) (ENNReal.ofReal p) ν
      ≤ eLpNorm (fun ℓ => M + (n 0 ℓ + n 1 ℓ)) (ENNReal.ofReal p) ν :=
        eLpNorm_mono_ae_real hDm hae
    _ ≤ eLpNorm (fun _ : LayerSample W .separate => M) (ENNReal.ofReal p) ν +
          (eLpNorm (n 0) (ENNReal.ofReal p) ν + eLpNorm (n 1) (ENNReal.ofReal p) ν) := by
        refine (eLpNorm_add_le (f := fun _ => M) (g := fun ℓ => n 0 ℓ + n 1 ℓ) hp1).trans ?_
        exact add_le_add le_rfl (eLpNorm_add_le (f := n 0) (g := n 1) hp1)
    _ ≤ ENNReal.ofReal M + (ENNReal.ofReal (Cp * (1 + u) / Real.sqrt W) +
          ENNReal.ofReal (Cp * (1 + u) / Real.sqrt W)) := by
        rw [fetR_eLpNorm_const hM0 hp0]
        exact add_le_add le_rfl (add_le_add (hn_le 0) (hn_le 1))
    _ = ENNReal.ofReal (M + (Cp * (1 + u) / Real.sqrt W + Cp * (1 + u) / Real.sqrt W)) := by
        rw [ENNReal.ofReal_add hM0 (by positivity), ENNReal.ofReal_add hN0 hN0]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hk1 : Cs * (1 + u) * (1 / W) ≤ Cs * (1 + u) * w :=
          mul_le_mul_of_nonneg_left hw1 (by positivity)
        have hk2 : Cp * (1 + u) / Real.sqrt W ≤ Cp * (1 + u) * w := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hw2 (by positivity)
        have hk3 : 0 ≤ Cp * ((1 + u) * δ) := by positivity
        have hd : fetDist b E X S = fetPathDist b E ω := rfl
        rw [hd] at hMle
        nlinarith

/-- **One step of the recursion in law** (`r ≥ 1`): under
`pathLaw (r+2) = (pathLaw r ⊗ layerLaw) ∘ (pgGrow ∘ swap)⁻¹`, with the regular part
(`δ_r ≤ d_*`, `fetR_cond` and Fubini) and the exit part weighted by `δ_r/d_* ≥ 1` (Hölder):
`a_{r+2} ≤ q a_r + C'‖(1+s_r)δ_r‖_p + C'w‖1+s_r‖_p + d_*⁻¹‖δ_r‖_{2p}‖D_{r+2}‖_{2p}`. -/
theorem fetR_step {b E p q Cs Cp dstar w : ℝ} (hb1 : b < 1 / 2) (hr : 1 ≤ r)
    (hE : E ∈ Set.Ioo (-2 : ℝ) 2) (hp : 1 ≤ p) (hq0 : 0 ≤ q) (hCs : 0 ≤ Cs) (hCp : 0 ≤ Cp)
    (hd : 0 < dstar) (hw1 : 1 / (W : ℝ) ≤ w) (hw2 : 1 / Real.sqrt W ≤ w)
    (hz : 0 < (boundaryZ b E).im)
    (hmean : ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      matchedDistance b E X ≤ dstar → ∀ j : Fin 2,
        ‖(∫ ℓ, fetGd b E X S ℓ j ∂layerLaw W b .separate) - tgtAd E‖ ≤
          q * fetDist b E X S + Cs * (1 + fetClock b E X S) * (matchedDistance b E X + 1 / W))
    (hnoise : ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      ∀ j : Fin 2, eLpNorm (fun ℓ => fetGd b E X S ℓ j -
          ∫ ℓ', fetGd b E X S ℓ' j ∂layerLaw W b .separate) (ENNReal.ofReal p)
          (layerLaw W b .separate) ≤ ENNReal.ofReal (Cp * (1 + fetClock b E X S) / Real.sqrt W))
    (hderiv : ∀ ω : PathSample W r, (∀ j, (ω.1 j).IsHermitian) →
      IsUnit (pathMatrix ω - (E : ℂ) • 1).det → ∀ j : Fin 2,
        ∀ᵐ ℓ ∂layerLaw W b .separate, HasDerivAt (fun E' : ℝ => (W : ℂ)⁻¹ *
          (meqPortProj (W := W) (σ := .separate) j *
            layerResolvent .separate E' (boundaryZ b E') (pathSchur E' ω) ℓ).trace)
          (fetGd b E (pathSchur E ω) (fetXd E ω) ℓ j) E) :
    eLpNorm (fun ω => fetPathDist b E ω) (ENNReal.ofReal p) (pathLaw W (r + 2) b) ≤
      ENNReal.ofReal q * eLpNorm (fun ω => fetPathDist b E ω) (ENNReal.ofReal p) (pathLaw W r b) +
      ENNReal.ofReal (Cs + 2 * Cp) * eLpNorm (fun ω => (1 + fetClock b E (pathSchur E ω)
        (fetXd E ω)) * matchedDistance b E (pathSchur E ω)) (ENNReal.ofReal p) (pathLaw W r b) +
      ENNReal.ofReal ((Cs + 2 * Cp) * w) * eLpNorm (fun ω => 1 + fetClock b E (pathSchur E ω)
        (fetXd E ω)) (ENNReal.ofReal p) (pathLaw W r b) +
      ENNReal.ofReal dstar⁻¹ * (eLpNorm (fun ω => matchedDistance b E (pathSchur E ω))
          (ENNReal.ofReal (2 * p)) (pathLaw W r b) *
        eLpNorm (fun ω => fetPathDist b E ω) (ENNReal.ofReal (2 * p)) (pathLaw W (r + 2) b)) := by
  have hpl := bond_isProbabilityMeasure_layerLaw W b .separate
  have hpr := fetR_isProb_path W r b
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hw0 : 0 ≤ w := le_trans (by positivity) hw2
  set μ := (pathLaw W r b).prod (layerLaw W b .separate) with hμ
  set Φ : PathSample W r × LayerSample W .separate → PathSample W (r + 2) :=
    fun x => pgGrow (x.2, x.1) with hΦ
  have hMP : MeasurePreserving Φ μ (pathLaw W (r + 2) b) :=
    (measurePreserving_pgGrow b hr).comp Measure.measurePreserving_swap
  set D : PathSample W (r + 2) → ℝ := fun ω => fetPathDist b E ω with hDdef
  have hDm : Measurable D := fetC_measurable_pathDist b E
  set s : PathSample W r → ℝ := fun ω => fetClock b E (pathSchur E ω) (fetXd E ω) with hsdef
  set δ : PathSample W r → ℝ := fun ω => matchedDistance b E (pathSchur E ω) with hδdef
  set d : PathSample W r → ℝ := fun ω => fetPathDist b E ω with hddef
  have hsm : Measurable s := fetR_measurable_clock b E
  have hδm : Measurable δ := fetR_measurable_dist b E
  have hdm : Measurable d := fetC_measurable_pathDist b E
  set C' := Cs + 2 * Cp with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set g : PathSample W r → ℝ := fun ω => q * d ω + C' * ((1 + s ω) * δ ω) + (C' * w) * (1 + s ω)
    with hgdef
  have hgm : Measurable g := by
    simp only [hgdef]
    fun_prop
  set F : PathSample W r × LayerSample W .separate → ℝ := D ∘ Φ with hFdef
  have hFm : Measurable F := hDm.comp hMP.measurable
  have hF0 : ∀ x, 0 ≤ F x := fun x => (norm_nonneg _).trans (le_max_left _ _)
  set Gs : Set (PathSample W r × LayerSample W .separate) :=
    Prod.fst ⁻¹' {ω | δ ω ≤ dstar} with hGs
  have hGsm : MeasurableSet Gs := measurable_fst (measurableSet_le hδm measurable_const)
  set F1 := Gs.indicator F with hF1
  set F2 : PathSample W r × LayerSample W .separate → ℝ := fun x => (dstar⁻¹ * δ x.1) * F x
    with hF2
  have hpt : ∀ x, ‖F x‖ ≤ ‖F1 x + F2 x‖ := by
    intro x
    have hδ0 : 0 ≤ δ x.1 := (norm_nonneg _).trans (le_max_left _ _)
    have h2 : 0 ≤ F2 x := mul_nonneg (mul_nonneg (inv_nonneg.mpr hd.le) hδ0) (hF0 x)
    by_cases hx : x ∈ Gs
    · have h1 : F1 x = F x := Set.indicator_of_mem hx F
      rw [h1, Real.norm_of_nonneg (hF0 x), Real.norm_of_nonneg (add_nonneg (hF0 x) h2)]
      linarith
    · have h1 : F1 x = 0 := Set.indicator_of_notMem hx F
      have hlt : dstar < δ x.1 := by
        simp only [hGs, Set.mem_preimage, Set.mem_ofPred_eq, not_le] at hx; exact hx
      have hge : 1 ≤ dstar⁻¹ * δ x.1 := by
        rw [← div_eq_inv_mul, le_div_iff₀ hd]; linarith
      rw [h1, zero_add, Real.norm_of_nonneg (hF0 x), Real.norm_of_nonneg h2]
      calc F x = 1 * F x := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hge (hF0 x)
  -- the regular part: conditional bound and Fubini
  have hprod : ∀ᵐ x ∂μ, IsUnit (pathMatrix (Φ x) - (E : ℂ) • 1).det ∧
      (pathSchur E (Φ x)).IsHermitian :=
    hMP.quasiMeasurePreserving.ae ((ae_isUnit_det_pathMatrix W (r + 2) hb1 E).and
      (srec_ae_pathSchur_isHermitian W (r + 2) b E))
  have hsec := Measure.ae_ae_of_ae_prod hprod
  have hF1le : eLpNorm F1 (ENNReal.ofReal p) μ ≤ eLpNorm g (ENNReal.ofReal p) (pathLaw W r b) := by
    have h := clk_eLpNorm_prod_le (μ := pathLaw W r b) (ν := layerLaw W b .separate) (F := F1)
      (g := g) (hFm.indicator hGsm) hgm hp0 (c := 1) ?_
    · rwa [ENNReal.ofReal_one, one_mul] at h
    filter_upwards [fetR_ae_blocks W r b, ae_isUnit_det_pathMatrix W r hb1 E, hsec] with ω hA hH hω
    rw [ENNReal.ofReal_one, one_mul]
    by_cases hgood : δ ω ≤ dstar
    · have e : (fun ℓ => F1 (ω, ℓ)) = fun ℓ => fetPathDist b E (pgGrow (ℓ, ω)) := by
        funext ℓ
        have hx : (ω, ℓ) ∈ Gs := hgood
        rw [hF1, Set.indicator_of_mem hx]
        rfl
      rw [e]
      refine (fetR_cond hr hE hp hCs hCp hw1 hw2 hz hmean hnoise ω hA hH hgood hω
        (hderiv ω hA hH)).trans (le_of_eq ?_)
      have hg0 : 0 ≤ g ω := by
        have hs0 : 0 ≤ s ω := clkTrace_nonneg ((fetR_xd_posSemidef hA E).conjTranspose_mul_mul_same _)
        have hδ0 : 0 ≤ δ ω := (norm_nonneg _).trans (le_max_left _ _)
        have hd0 : 0 ≤ d ω := (norm_nonneg _).trans (le_max_left _ _)
        positivity
      rw [Real.enorm_of_nonneg hg0]
    · have e : (fun ℓ => F1 (ω, ℓ)) = 0 := by
        funext ℓ
        have hx : (ω, ℓ) ∉ Gs := hgood
        rw [hF1, Set.indicator_of_notMem hx]
        rfl
      rw [e, eLpNorm_zero]
      exact bot_le
  -- the exit part: Hölder
  have hF2le : eLpNorm F2 (ENNReal.ofReal p) μ ≤ ENNReal.ofReal dstar⁻¹ *
      (eLpNorm δ (ENNReal.ofReal (2 * p)) (pathLaw W r b) *
        eLpNorm D (ENNReal.ofReal (2 * p)) (pathLaw W (r + 2) b)) := by
    have hfm : Measurable (fun x : PathSample W r × LayerSample W .separate => dstar⁻¹ * δ x.1) :=
      measurable_const.mul (hδm.comp measurable_fst)
    have h := wl_eLpNorm_mul_le (μ := μ) hfm.aestronglyMeasurable hFm.aestronglyMeasurable hp0
    refine h.trans (le_of_eq ?_)
    rw [fetR_eLpNorm_smul (f := fun x : PathSample W r × LayerSample W .separate => δ x.1)
      (inv_nonneg.mpr hd.le), mul_assoc]
    congr 2
    · exact eLpNorm_comp_measurePreserving (f := Prod.fst) hδm.aestronglyMeasurable
        measurePreserving_fst
    · exact eLpNorm_comp_measurePreserving hDm.aestronglyMeasurable hMP
  -- the regular majorant
  have hgle : eLpNorm g (ENNReal.ofReal p) (pathLaw W r b) ≤
      ENNReal.ofReal q * eLpNorm d (ENNReal.ofReal p) (pathLaw W r b) +
      ENNReal.ofReal C' * eLpNorm (fun ω => (1 + s ω) * δ ω) (ENNReal.ofReal p) (pathLaw W r b) +
      ENNReal.ofReal (C' * w) * eLpNorm (fun ω => 1 + s ω) (ENNReal.ofReal p) (pathLaw W r b) := by
    refine (eLpNorm_add_le (f := fun ω => q * d ω + C' * ((1 + s ω) * δ ω))
      (g := fun ω => (C' * w) * (1 + s ω)) hp1).trans (add_le_add ?_ ?_)
    · refine (eLpNorm_add_le (f := fun ω => q * d ω) (g := fun ω => C' * ((1 + s ω) * δ ω))
        hp1).trans (add_le_add ?_ ?_)
      · rw [fetR_eLpNorm_smul hq0]
      · rw [fetR_eLpNorm_smul hC'0]
    · rw [fetR_eLpNorm_smul (mul_nonneg hC'0 hw0)]
  calc eLpNorm D (ENNReal.ofReal p) (pathLaw W (r + 2) b) = eLpNorm F (ENNReal.ofReal p) μ :=
        (eLpNorm_comp_measurePreserving hDm.aestronglyMeasurable hMP).symm
    _ ≤ eLpNorm (fun x => F1 x + F2 x) (ENNReal.ofReal p) μ :=
        eLpNorm_mono hFm.aestronglyMeasurable hpt
    _ ≤ eLpNorm F1 (ENNReal.ofReal p) μ + eLpNorm F2 (ENNReal.ofReal p) μ :=
        eLpNorm_add_le (f := F1) (g := F2) hp1
    _ ≤ _ := by
        refine (add_le_add (hF1le.trans hgle) hF2le).trans (le_of_eq ?_)
        rfl

end Step

/-!
## 4. Moments along the path
-/

section Moments

variable {W r : ℕ}

/-- The full energy clock under `pathLaw` is the clock of the clock-moments lemma. -/
theorem fetR_eLpNorm_clock_eq (b E : ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun ω => fetClock b E (pathSchur E ω) (fetXd E ω)) q (pathLaw W r b) =
      eLpNorm (fun ω => clkTrace (clkCoreSource b E (fun _ => true) ω)) q (pathLaw W r b) := by
  refine eLpNorm_congr_ae ?_
  filter_upwards [fetR_ae_blocks W r b] with ω hA
  exact fetR_clock_eq hA

/-- **Crude moments** of the derivative distance: `‖D_r‖_q ≤ ‖s_r‖_q + C₀`. -/
theorem fetR_eLpNorm_D_le {b E η Z A q : ℝ} (hq : 1 ≤ q) (hη : 0 < η)
    (hz : η ≤ (boundaryZ b E).im) (hZ : ‖tgtZd b E‖ ≤ Z) (hA : ‖tgtAd E‖ ≤ A) :
    eLpNorm (fun ω => fetPathDist b E ω) (ENNReal.ofReal q) (pathLaw W r b) ≤
      eLpNorm (fun ω => fetClock b E (pathSchur E ω) (fetXd E ω)) (ENNReal.ofReal q)
        (pathLaw W r b) + ENNReal.ofReal (Z * (η⁻¹) ^ 2 + A) := by
  have hpr := fetR_isProb_path W r b
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr hq
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA
  have hC0 : 0 ≤ Z * (η⁻¹) ^ 2 + A := by positivity
  have hae : ∀ᵐ ω ∂pathLaw W r b, ‖fetPathDist b E ω‖ ≤
      fetClock b E (pathSchur E ω) (fetXd E ω) + (Z * (η⁻¹) ^ 2 + A) := by
    filter_upwards [fetR_ae_blocks W r b] with ω hA'
    have h0 : 0 ≤ fetPathDist b E ω := (norm_nonneg _).trans (le_max_left _ _)
    rw [Real.norm_of_nonneg h0]
    exact fetR_dist_le (srec_pathSchur_isHermitian E ω hA') (fetR_xd_posSemidef hA' E) hη hz hZ hA
  refine (eLpNorm_mono_ae_real (fetC_measurable_pathDist b E).aestronglyMeasurable hae).trans ?_
  refine (eLpNorm_add_le (f := fun ω => fetClock b E (pathSchur E ω) (fetXd E ω))
    (g := fun _ => Z * (η⁻¹) ^ 2 + A) hq1).trans ?_
  rw [fetR_eLpNorm_const hC0 (by linarith)]

/-- The recursion arithmetic: `qAx + C'(1 + C_u x)D w + C'w(1 + C_u x) +
d_*⁻¹ D w (C_u(x+2) + C₀) ≤ A(x+2)w` for `x ≥ 1`, `A = C_c + B/(1-q)`. -/
theorem fetR_arith {q A B C' Cu Dδ dinv C₀ Cc x w : ℝ} (hq1 : q < 1)
    (hC' : 0 ≤ C') (hCu : 0 ≤ Cu) (hDδ : 0 ≤ Dδ) (hdinv : 0 ≤ dinv) (hC₀ : 0 ≤ C₀) (hCc : 0 ≤ Cc)
    (hx : 1 ≤ x) (hw : 0 ≤ w)
    (hB : B = C' * (1 + Cu) * Dδ + C' * (1 + Cu) + dinv * Dδ * (3 * Cu + C₀))
    (hA : A = Cc + B / (1 - q)) :
    q * (A * x * w) + C' * ((1 + Cu * x) * (Dδ * w)) + C' * w * (1 + Cu * x) +
        dinv * (Dδ * w * (Cu * (x + 2) + C₀)) ≤ A * (x + 2) * w := by
  have h1q : 0 < 1 - q := by linarith
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hqA : q * A + B ≤ A := by
    have e : B = (1 - q) * (B / (1 - q)) := by field_simp
    rw [hA]; nlinarith
  have k1 : 1 + Cu * x ≤ (1 + Cu) * x := by nlinarith
  have k2 : Cu * (x + 2) + C₀ ≤ (3 * Cu + C₀) * x := by nlinarith
  have e1 : C' * ((1 + Cu * x) * (Dδ * w)) ≤ C' * ((1 + Cu) * x * (Dδ * w)) := by gcongr
  have e2 : C' * w * (1 + Cu * x) ≤ C' * w * ((1 + Cu) * x) := by gcongr
  have e3 : dinv * (Dδ * w * (Cu * (x + 2) + C₀)) ≤ dinv * (Dδ * w * ((3 * Cu + C₀) * x)) := by
    gcongr
  have e4 : (q * A + B) * (x * w) ≤ A * (x * w) := by gcongr
  have e5 : A * x * w ≤ A * (x + 2) * w := by gcongr; linarith
  have e6 : q * (A * x * w) + C' * ((1 + Cu) * x * (Dδ * w)) + C' * w * ((1 + Cu) * x) +
      dinv * (Dδ * w * ((3 * Cu + C₀) * x)) = (q * A + B) * (x * w) := by rw [hB]; ring
  nlinarith

theorem fetR_ofReal_add4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d =
      ENNReal.ofReal (a + b + c + d) := by
  rw [ENNReal.ofReal_add (add_nonneg (add_nonneg ha hb) hc) hd,
    ENNReal.ofReal_add (add_nonneg ha hb) hc, ENNReal.ofReal_add ha hb]

end Moments

/-!
## 5. `FetPathBound`
-/

/-- **The path clause of the energy paragraph** (`FetPathBound`: "the full clock bound proves
`‖f'_r - a'‖_{L^p} ≤ C_p(r+1)/√W`"), from `ConditionalBlockGUECount` and `GaussianLpGradient`.

*Law:* `pathLaw W r b` (independent `GUE_W(c/W)` blocks, `Gin(b/W)` bonds and port bonds).
*Objects:* `f'_{r,i} = fetFd(X_r, X_r')_i` the exact energy derivative of `W⁻¹ Tr(R_r)_{ii}`
(`R_r = (z_∂ - X_r)⁻¹`, `X_r = pathSchur E ω`, `X_r' = fetXd E ω`), `D_r = max_i |f'_{r,i} - a'|`
(`fetPathDist`). *Domain:* deterministic `E ∈ bulkInterval κ`, `1 ≤ r ≤ TW`, both parities.
*Norms:* `L^p(pathLaw W r b)` of the real scalar `D_r`.
*Quantifiers:* `b ∈ (0, 1/2)`, `κ > 0`, `T` and `p ≥ 1` first; then `C ≥ 0`, `W₀`; uniformly in
`W ≥ W₀`, `r` and `E`: `‖D_r‖_p ≤ C(r+1)/√W`.
*Proof:* the recursion `a_{r+2} ≤ q a_r + B(r+1)/√W` (`fetR_step`, `fetR_arith`) from the cores
(`fetCoreBound_holds`), with `fetStepMean_holds`, the energy and noise clauses of
`diffCovarianceFamily_holds'`, `clockMoments_holds` (order `2p`) and `matchedTraces_holds` (path
clause, order `2p`). -/
theorem fetPathBound_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) : FetPathBound := by
  intro b hb0 hb1 κ T hκ p hp
  obtain ⟨dstar, q, Cs, W₁, hdstar, hq0, hq1, hCs, hmean⟩ :=
    fetStepMean_holds hcount hgrad b hb0 hb1 κ hκ
  obtain ⟨Cc, W₂, hCc, hcore⟩ := fetCoreBound_holds hcount hgrad b hb0 hb1 κ hκ p hp
  obtain ⟨-, ⟨Ce, W₃, hen⟩, hno⟩ := diffCovarianceFamily_holds' hcount hgrad b hb0 hb1 κ hκ
  obtain ⟨Cp₀, W₄, hnoise⟩ := hno p hp
  obtain ⟨Cu, W₅, hCu, hclk⟩ :=
    clockMoments_holds hcount hgrad b hb0 hb1 κ T hκ (2 * p) (by linarith)
  obtain ⟨ε₀, Cδ, hε₀, hδ⟩ := (matchedTraces_holds hcount hgrad).path b hb0 hb1 κ T hκ
  obtain ⟨η, hη, hηE⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  obtain ⟨A₁, ι, hA₁, -, hscal⟩ := fetS_scal_bounds hb0.le hκ
  set Z := (b + 1) / Real.sqrt (2 * κ) with hZdef
  have hZ0 : 0 ≤ Z := by positivity
  set C₀ := Z * (η⁻¹) ^ 2 + A₁ with hC₀def
  have hC₀ : 0 ≤ C₀ := by positivity
  set Cp := max Cp₀ 0 with hCpdef
  have hCp : 0 ≤ Cp := le_max_right _ _
  set C' := Cs + 2 * Cp with hC'def
  have hC' : 0 ≤ C' := by positivity
  set Dδ := max Cδ 0 * Real.sqrt (2 * p) with hDδdef
  have hDδ : 0 ≤ Dδ := by positivity
  set B := C' * (1 + Cu) * Dδ + C' * (1 + Cu) + dstar⁻¹ * Dδ * (3 * Cu + C₀) with hBdef
  set A := Cc + B / (1 - q) with hAdef
  have h1q : 0 < 1 - q := by linarith
  have hB0 : 0 ≤ B := by positivity
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A, max (max (max W₁ W₂) (max W₃ W₄)) (max W₅ ⌈2 * p / ε₀⌉₊), hA0, ?_⟩
  intro W hW hWW
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hWW)
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hWW)
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hWW)
  have hW4 : W₄ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hWW)
  have hW5 : W₅ ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hWW)
  have hW6 : ⌈2 * p / ε₀⌉₊ ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hWW)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hWge : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hsq0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWr
  have hsqW : Real.sqrt W ≤ W := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set w := 1 / Real.sqrt W with hwdef
  have hw0 : 0 ≤ w := by positivity
  have hw1 : 1 / (W : ℝ) ≤ w := one_div_le_one_div_of_le hsq0 hsqW
  have hw2 : 1 / Real.sqrt W ≤ w := le_rfl
  have h2pW : 2 * p ≤ ε₀ * W := by
    have h := (Nat.le_ceil (2 * p / ε₀)).trans (by exact_mod_cast hW6 : (⌈2 * p / ε₀⌉₊ : ℝ) ≤ W)
    rw [div_le_iff₀ hε₀] at h; linarith
  intro r hr hrT E hE
  have hEabs : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  have hEI : E ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [(abs_lt.mp hEabs).1], (abs_lt.mp hEabs).2⟩
  obtain ⟨hzη, -⟩ := hηE E hE
  have hz : 0 < (boundaryZ b E).im := hη.trans_le hzη
  have hZE : ‖tgtZd b E‖ ≤ Z := tgt_norm_tgtZd_le hb0.le hκ hE
  have hAE : ‖tgtAd E‖ ≤ A₁ := (hscal E hE).1
  -- the inputs at this `W`, `E`
  have hmean' : ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      matchedDistance b E X ≤ dstar → ∀ j : Fin 2,
        ‖(∫ ℓ, fetGd b E X S ℓ j ∂layerLaw W b .separate) - tgtAd E‖ ≤
          q * fetDist b E X S + Cs * (1 + fetClock b E X S) * (matchedDistance b E X + 1 / W) :=
    fun X S hX hS hd j => hmean W hW hW1 X S hX hS E hE hd j
  have hnoise' : ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
      ∀ j : Fin 2, eLpNorm (fun ℓ => fetGd b E X S ℓ j -
          ∫ ℓ', fetGd b E X S ℓ' j ∂layerLaw W b .separate) (ENNReal.ofReal p)
          (layerLaw W b .separate) ≤ ENNReal.ofReal (Cp * (1 + fetClock b E X S) / Real.sqrt W) := by
    intro X S hX hS j
    have hu0 : 0 ≤ fetClock b E X S := clkTrace_nonneg (hS.conjTranspose_mul_mul_same _)
    have h := (hnoise W hW hW4 X S hX hS E hE (meqPortProj (W := W) (σ := .separate) j)
      (meq_norm_portProj_le (W := W) (σ := .separate) j)).2.2
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by linarith [hu0] : (0 : ℝ) ≤ 1 + fetClock b E X S)) (Real.sqrt_nonneg _)
  have hderiv' : ∀ r' : ℕ, ∀ ω : PathSample W r', (∀ j, (ω.1 j).IsHermitian) →
      IsUnit (pathMatrix ω - (E : ℂ) • 1).det → ∀ j : Fin 2,
        ∀ᵐ ℓ ∂layerLaw W b .separate, HasDerivAt (fun E' : ℝ => (W : ℂ)⁻¹ *
          (meqPortProj (W := W) (σ := .separate) j *
            layerResolvent .separate E' (boundaryZ b E') (pathSchur E' ω) ℓ).trace)
          (fetGd b E (pathSchur E ω) (fetXd E ω) ℓ j) E := fun r' ω hA hH j =>
    (hen W hW hW3 (fun E' => pathSchur E' ω) (fetXd E ω) E 1 hE one_pos (fetR_xd_posSemidef hA E)
      (fetC_hasDerivAt_pathSchur E ω hH) (fun E' _ => srec_pathSchur_isHermitian E' ω hA)
      (meqPortProj (W := W) (σ := .separate) j) (meq_norm_portProj_le (W := W) (σ := .separate) j)).2.1
  -- moments at order `2p`
  have hs2p : ∀ r' : ℕ, 1 ≤ r' → (r' : ℝ) ≤ T * W →
      eLpNorm (fun ω => fetClock b E (pathSchur E ω) (fetXd E ω)) (ENNReal.ofReal (2 * p))
        (pathLaw W r' b) ≤ ENNReal.ofReal (Cu * ((r' : ℝ) + 1)) := by
    intro r' hr' hr'T
    rw [fetR_eLpNorm_clock_eq]
    exact (hclk W hW5 hW).1 r' hr' hr'T E hE
  have hδ2p : ∀ r' : ℕ, 1 ≤ r' → (r' : ℝ) ≤ T * W →
      eLpNorm (fun ω => matchedDistance b E (pathSchur E ω)) (ENNReal.ofReal (2 * p))
        (pathLaw W r' b) ≤ ENNReal.ofReal (Dδ * w) := by
    intro r' hr' hr'T
    refine (hδ W hW (2 * p) (by linarith) h2pW r' hr' hr'T E hE).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Cδ * Real.sqrt (2 * p) ≤ max Cδ 0 * Real.sqrt (2 * p) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    have h2 : 0 ≤ max Cδ 0 * Real.sqrt (2 * p) := by positivity
    calc Cδ * Real.sqrt (2 * p) / W ≤ max Cδ 0 * Real.sqrt (2 * p) / W :=
          div_le_div_of_nonneg_right h1 hWr.le
      _ ≤ max Cδ 0 * Real.sqrt (2 * p) / Real.sqrt W := div_le_div_of_nonneg_left h2 hsq0 hsqW
      _ = Dδ * w := by rw [hDδdef, hwdef]; ring
  -- the recursion
  suffices hrec : ∀ r' : ℕ, 1 ≤ r' → (r' : ℝ) ≤ T * W →
      eLpNorm (fun ω => fetPathDist b E ω) (ENNReal.ofReal p) (pathLaw W r' b) ≤
        ENNReal.ofReal (A * ((r' : ℝ) + 1) / Real.sqrt W) from hrec r hr hrT
  intro r'
  induction r' using Nat.strong_induction_on with
  | _ r' ih =>
  intro hr' hr'T
  by_cases hr2 : r' ≤ 2
  · have hcr : r' = 1 ∨ r' = 2 := by omega
    refine (hcore W hW hW2 r' hcr E hE).trans (ENNReal.ofReal_le_ofReal ?_)
    refine div_le_div_of_nonneg_right ?_ hsq0.le
    have hCA : Cc ≤ A := by rw [hAdef]; have := div_nonneg hB0 h1q.le; linarith
    have hr1 : (1 : ℝ) ≤ (r' : ℝ) + 1 := by have := (Nat.cast_nonneg r' : (0 : ℝ) ≤ r'); linarith
    nlinarith
  obtain ⟨k, rfl⟩ : ∃ k, r' = k + 2 := ⟨r' - 2, by omega⟩
  have hk : 1 ≤ k := by omega
  have hkT : (k : ℝ) ≤ T * W := le_trans (by exact_mod_cast (by omega : k ≤ k + 2)) hr'T
  have hih := ih k (by omega) hk hkT
  have hst := fetR_step (W := W) (r := k) hb1 hk hEI hp hq0 hCs hCp hdstar hw1 hw2 hz hmean'
    hnoise' (hderiv' k)
  have hpr := fetR_isProb_path W k b
  have h2p1 : 1 ≤ 2 * p := by linarith
  have hs := hs2p k hk hkT
  have hδk := hδ2p k hk hkT
  set x : ℝ := (k : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  have hux : 0 ≤ 1 + Cu * x := by positivity
  have hDw : 0 ≤ Dδ * w := by positivity
  have hP1s : eLpNorm (fun ω => 1 + fetClock b E (pathSchur E ω) (fetXd E ω))
      (ENNReal.ofReal (2 * p)) (pathLaw W k b) ≤ ENNReal.ofReal (1 + Cu * x) := by
    refine (fetR_eLpNorm_one_add h2p1).trans ?_
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
    exact add_le_add le_rfl hs
  have hP1 : eLpNorm (fun ω => (1 + fetClock b E (pathSchur E ω) (fetXd E ω)) *
      matchedDistance b E (pathSchur E ω)) (ENNReal.ofReal p) (pathLaw W k b) ≤
      ENNReal.ofReal ((1 + Cu * x) * (Dδ * w)) := by
    refine (wl_eLpNorm_mul_le ((fetR_measurable_clock b E).const_add 1).aestronglyMeasurable
      (fetR_measurable_dist b E).aestronglyMeasurable (by linarith : (0 : ℝ) < p)).trans ?_
    rw [ENNReal.ofReal_mul hux]
    exact mul_le_mul' hP1s hδk
  have hP2 : eLpNorm (fun ω => 1 + fetClock b E (pathSchur E ω) (fetXd E ω)) (ENNReal.ofReal p)
      (pathLaw W k b) ≤ ENNReal.ofReal (1 + Cu * x) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans hP1s
  have hP4 : eLpNorm (fun ω => fetPathDist b E ω) (ENNReal.ofReal (2 * p)) (pathLaw W (k + 2) b) ≤
      ENNReal.ofReal (Cu * (x + 2) + C₀) := by
    refine (fetR_eLpNorm_D_le h2p1 hη hzη hZE hAE).trans ?_
    rw [ENNReal.ofReal_add (by positivity) hC₀]
    refine add_le_add ((hs2p (k + 2) hr' hr'T).trans (le_of_eq ?_)) le_rfl
    congr 1; rw [hx]; push_cast; ring
  have hdinv : 0 ≤ dstar⁻¹ := inv_nonneg.mpr hdstar.le
  have hAx : A * x / Real.sqrt W = A * x * w := by rw [hwdef]; ring
  have hfin := fetR_arith (q := q) (A := A) (B := B) (C' := C') (Cu := Cu) (Dδ := Dδ)
    (dinv := dstar⁻¹) (C₀ := C₀) (Cc := Cc) (x := x) (w := w) hq1 hC' hCu hDδ hdinv hC₀ hCc hx1
    hw0 hBdef hAdef
  refine hst.trans ?_
  calc _ ≤ ENNReal.ofReal q * ENNReal.ofReal (A * x / Real.sqrt W) +
        ENNReal.ofReal C' * ENNReal.ofReal ((1 + Cu * x) * (Dδ * w)) +
        ENNReal.ofReal (C' * w) * ENNReal.ofReal (1 + Cu * x) +
        ENNReal.ofReal dstar⁻¹ * (ENNReal.ofReal (Dδ * w) * ENNReal.ofReal (Cu * (x + 2) + C₀)) := by
        gcongr
    _ = ENNReal.ofReal (q * (A * x * w) + C' * ((1 + Cu * x) * (Dδ * w)) + C' * w * (1 + Cu * x) +
          dstar⁻¹ * (Dδ * w * (Cu * (x + 2) + C₀))) := by
        rw [hAx, ← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_mul hC',
          ← ENNReal.ofReal_mul (mul_nonneg hC' hw0), ← ENNReal.ofReal_mul hDw,
          ← ENNReal.ofReal_mul hdinv]
        have h1 : 0 ≤ q * (A * x * w) :=
          mul_nonneg hq0 (mul_nonneg (mul_nonneg hA0 (by linarith)) hw0)
        have h2 : 0 ≤ C' * ((1 + Cu * x) * (Dδ * w)) := mul_nonneg hC' (mul_nonneg hux hDw)
        have h3 : 0 ≤ C' * w * (1 + Cu * x) := mul_nonneg (mul_nonneg hC' hw0) hux
        have h4 : 0 ≤ dstar⁻¹ * (Dδ * w * (Cu * (x + 2) + C₀)) :=
          mul_nonneg hdinv (mul_nonneg hDw (add_nonneg (mul_nonneg hCu (by linarith)) hC₀))
        exact fetR_ofReal_add4 h1 h2 h3 h4
    _ ≤ ENNReal.ofReal (A * (((k + 2 : ℕ) : ℝ) + 1) / Real.sqrt W) := by
        have e : A * (x + 2) * w = A * (((k + 2 : ℕ) : ℝ) + 1) / Real.sqrt W := by
          rw [hwdef, hx]; push_cast; ring
        exact ENNReal.ofReal_le_ofReal (hfin.trans_eq e)

end BlockBand.Layers
