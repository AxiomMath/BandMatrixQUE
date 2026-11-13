module

public import BlockBand.Endpoints.Poisson.SingleCollarStageCompare
public import BlockBand.Endpoints.Poisson.SingleCollarStageLimsup

/-!
# The single-collar log-error bound at one stage configuration

Law: the original prior in Gaussian coordinates.

* `ScsWardData`, `ScsWardScattering` (a hypothesis): the Ward and scattering data of one stage
  configuration.
* `ScsStageLogMoment` (a hypothesis): the `L^r` bound of the stage log difference
  (exceptional-set removal through the effective block model).
* `scs_stage_bound`: the single-collar log-error bound at one stage configuration.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace intervalSource growthPathLaw)
open BlockBand.Endpoints.PhaseFractional (schattenFrac scatteringDistance)
open BlockBand.Internal.Contracts.Critical (CollarKernelContract collarScattering oldScattering
  conductance)
open BlockBand.Internal.Contracts.Layers (bulkInterval boundaryZ matchedDistance)
open scoped ENNReal ComplexOrder

/-!
## 1. The Ward/scattering identification
-/

/-- **Ward/scattering data of one stage configuration** (the remote scattering source, with the
signed source update, and the identification of `Q_C`). Old coordinates `o = oldCoords L s k ω`; `η = Im z_b(e)`.

* `β`: the other input ports (the endpoint matched leads of the old network);
* `S₀`, `S₁`: the complete scattering matrices without and with the absorber `iκP_C/W²`,
  measurable in `o`; `S₀` unitary and `S₁` a contraction for every `o`;
* `Q = W⁻² U_lead* P_C U_lead ⪰ 0` with `Tr|S₁ - S₀|^q ≤ (2ηκ)^q Tr Q^q` (`0 < q ≤ 2`) and
  `I - S₁*S₁ ⪯ 4ηκ Q`;
* almost surely the collar blocks are the compressed responses `r₀`, `r_κ`
  (`scsResponse`, the `r_κ` of the stage factorization);
* the old network has at most `m` components (unused slots have length `0`), of lengths
  `len i ≤ n`; for every source profile `qs i ∈ [0,1]` equal to `1` on the scaled source window
  `[(buf-2)/W, (len i - buf + 2)/W]` of component `i` (the blocks of `C` lie at distance at
  least `buf` from both ends of their component), there are matrices `Qc i` with the law of the
  interval source `intervalSource b e W (len i) (qs i)` of a path under `growthPathLaw`
  and `Tr Q^q ≤ Σ_i Tr (Qc i)^q` almost surely for `0 < q < 1` (block-diagonality of `Q_C`
  over components and monotonicity of the interval source in the profile). -/
structure ScsWardData (P : Parameters) {m : ℕ} (L : Fin m → ℕ) (s : ZMod P.n) (π : Pairing)
    (S : Finset (Fin m)) (k : Fin m) (e : ℝ) (buf : ℕ) (κ : ℝ) where
  β : Type
  [fβ : Fintype β]
  [dβ : DecidableEq β]
  S₀ : (oldCoordSet L s k → Matrix (Fin P.W) (Fin P.W) ℂ) →
    Matrix ((Fin 2 × Fin P.W) ⊕ β) ((Fin 2 × Fin P.W) ⊕ β) ℂ
  S₁ : (oldCoordSet L s k → Matrix (Fin P.W) (Fin P.W) ℂ) →
    Matrix ((Fin 2 × Fin P.W) ⊕ β) ((Fin 2 × Fin P.W) ⊕ β) ℂ
  Q : (oldCoordSet L s k → Matrix (Fin P.W) (Fin P.W) ℂ) →
    Matrix ((Fin 2 × Fin P.W) ⊕ β) ((Fin 2 × Fin P.W) ⊕ β) ℂ
  measurable_S₀ : Measurable S₀
  measurable_S₁ : Measurable S₁
  measurable_Q : Measurable Q
  unitary : ∀ o, (S₀ o)ᴴ * S₀ o = 1
  contraction : ∀ o, (1 - (S₁ o)ᴴ * S₁ o).PosSemidef
  posSemidef_Q : ∀ o, (Q o).PosSemidef
  ward_diff : ∀ o (q : ℝ), 0 < q → q ≤ 2 →
    schattenFrac q (S₁ o - S₀ o) ≤ (2 * (boundaryZ P.b e).im * κ) ^ q * fracTrace q (Q o)
  ward_defect : ∀ o,
    ((((4 * (boundaryZ P.b e).im * κ : ℝ)) : ℂ) • Q o - (1 - (S₁ o)ᴴ * S₁ o)).PosSemidef
  block₀ : ∀ᵐ ω ∂(ringCoordLaw P.n P.W P.b),
    (S₀ (oldCoords L s k ω)).toBlocks₁₁ = scsResponse P L s π S k P.b e buf 0 ω
  block₁ : ∀ᵐ ω ∂(ringCoordLaw P.n P.W P.b),
    (S₁ (oldCoords L s k ω)).toBlocks₁₁ = scsResponse P L s π S k P.b e buf κ ω
  len : Fin m → ℕ
  len_le : ∀ i, len i ≤ P.n
  paths : ∀ qs : Fin m → ℝ → ℝ, (∀ i x, 0 ≤ qs i x ∧ qs i x ≤ 1) →
    (∀ i, ∀ x ∈ Icc (((buf : ℝ) - 2) / P.W) (((len i : ℝ) - buf + 2) / P.W), qs i x = 1) →
    ∃ Qc : Fin m → RingCoords P.n P.W → Matrix (Fin 2 × Fin P.W) (Fin 2 × Fin P.W) ℂ,
      (∀ i, Measurable (Qc i)) ∧
      (∀ i, (ringCoordLaw P.n P.W P.b).map (Qc i) =
        (growthPathLaw P.W P.b).map (intervalSource P.b e P.W (len i) (qs i))) ∧
      ∀ᵐ ω ∂(ringCoordLaw P.n P.W P.b), ∀ q : ℝ, 0 < q → q < 1 →
        fracTrace q (Q (oldCoords L s k ω)) ≤ ∑ i, fracTrace q (Qc i ω)

attribute [instance] ScsWardData.fβ ScsWardData.dβ

/-- **Ward/scattering data exist** at every stage configuration: the remote scattering source,
obtained from the exact resolvent and Ward identities with the contraction `(I + iκK_C/W²)⁻¹`
of the signed source update, and `Q_C` on the at most `m` components.

This is strictly weaker than `ScStageLogErrorPointwise`: it is a statement about the old network
alone (no fresh collar, no log-determinant, no expectation of a log, no limit in `W`, no
exceptional set), at one configuration. -/
def ScsWardScattering : Prop :=
  ∀ (P : Parameters) {m : ℕ} (L : Fin m → ℕ), IsCollarLayout P.n L → ∀ (π : Pairing)
    (S : Finset (Fin m)) (k : Fin m), k ∉ S → ∀ (buf : ℕ) (e : ℝ), -2 < e → e < 2 →
    ∀ κ : ℝ, 0 ≤ κ → Nonempty (ScsWardData P L 0 π S k e buf κ)

/-!
## 2. The exceptional-set log moment
-/

/-- The stage log difference `B^{π,S}_κ(e) - B^{π,S∪{k}}_κ(e)` (base block `0`, `z = z_b(e)`). -/
def scsStageLogDiff (P : Parameters) {m : ℕ} (L : Fin m → ℕ) (π : Pairing) (S : Finset (Fin m))
    (k : Fin m) (e : ℝ) (buf : ℕ) (κ : ℝ) (ω : RingCoords P.n P.W) : ℝ :=
  Real.log (‖(stageMatrix L 0 π S e (boundaryZ P.b e) buf κ ω).det‖ /
      ‖(stageMatrix L 0 π S e (boundaryZ P.b e) buf 0 ω).det‖) -
    Real.log (‖(stageMatrix L 0 π (insert k S) e (boundaryZ P.b e) buf κ ω).det‖ /
      ‖(stageMatrix L 0 π (insert k S) e (boundaryZ P.b e) buf 0 ω).det‖)

/-- **Stage log moment**: for `0 < b < 1/2` and `K ≥ 0` there are `r > 1` and `M` with
`‖B^{π,S}_κ(e) - B^{π,S∪{k}}_κ(e)‖_{L^r} ≤ M` under the original prior, uniformly in the
parameters with bond `b`, the layout, pairing, stage, buffer, `e ∈ (-2, 2)` and `κ ≥ 0` with
`κn/W ≤ K`.

This is strictly weaker than `ScStageLogErrorPointwise`: it is a uniform moment bound only (each
`B ≥ 0` is controlled separately); it carries no comparison of the two stages and no decay in
`R`. -/
def ScsStageLogMoment : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ K : ℝ, 0 ≤ K → ∃ r M : ℝ, 1 < r ∧
    ∀ (P : Parameters), P.b = b → ∀ {m : ℕ} (L : Fin m → ℕ), IsCollarLayout P.n L →
    ∀ (π : Pairing) (S : Finset (Fin m)) (k : Fin m), k ∉ S → ∀ (buf : ℕ) (e : ℝ), -2 < e → e < 2 →
    ∀ κ : ℝ, 0 ≤ κ → κ * P.n / P.W ≤ K →
      eLpNorm (scsStageLogDiff P L π S k e buf κ) (ENNReal.ofReal r)
        (ringCoordLaw P.n P.W P.b) ≤ ENNReal.ofReal M

/-!
## 3. The bound at one configuration
-/

/-- The Ward majorant of `σ` (right side of `sc_source_unitary_dilation`). -/
def scsSigmaBound (p η κ : ℝ) {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℂ) : ℝ :=
  2 ^ (p / 2) * (2 * ((2 * η * κ) ^ p * fracTrace p Q + (4 * η * κ) ^ (p / 2) * fracTrace (p / 2) Q))

theorem scs_continuous_scatteringDistance (b e : ℝ) (W : ℕ) :
    Continuous (fun r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => scatteringDistance b e r) := by
  unfold scatteringDistance BlockBand.Internal.Contracts.Layers.blockTrace
  refine Continuous.max ?_ ?_ <;>
  · refine (Continuous.sub ?_ continuous_const).norm
    refine continuous_const.mul (continuous_finsetSum _ fun a _ => ?_)
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    exact continuous_const.mul (continuous_const.sub (continuous_apply_apply _ _))

theorem scs_measurable_toCriticalCollar (W : ℕ) :
    Measurable (toCriticalCollar (W := W)) := by
  unfold toCriticalCollar
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
  · refine Measurable.of_eval fun i => ?_
    fin_cases i <;> simp <;> exact (measurable_pi_apply _).comp measurable_fst
  · refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun _ => ?_
    by_cases ha : a = 0
    · simp only [ha, ite_true]; exact (measurable_pi_apply _).comp measurable_snd
    · simp only [ha, ite_false]
      exact measurable_conjTranspose''.comp ((measurable_pi_apply _).comp measurable_snd)
  · exact Measurable.of_eval_matrix _ fun _ _ => by
      simp only [submatrix_apply]
      exact Matrix.measurable_apply.comp ((measurable_pi_apply _).comp measurable_fst)

/-- **The single-collar log-error bound at one stage configuration**, from `CollarKernelContract`:
`d₂, c_* > 0`, `W₀`, and for each `0 < p < 1` a `C_p ≥ 0`
such that for every admissible `P` with `P.b = b`, `W ≥ W₀`, collar layout, pairing, stage,
collar `k ∉ S`, buffer, bulk energy `e ∈ bulkInterval κI`, source `κ ≥ 0` and Ward data `D`:
if `E (g₀ ∨ 0)² ≤ C_g` (`g₀ = conductance r₀`), `E(σ̄ + σ̄²) ≤ A`
(`σ̄ = scsSigmaBound p η κ Q`), `‖ΔB‖_{L^r} ≤ M` with `r > 1`, and `P(d(X₀) > d₂) ≤ ε₁`, then
`E|ΔB| ≤ C_p (A + √C_g √A) + M (ε₁ + A/(c_* W))^{1-1/r}`.
-/
theorem scs_stage_bound (hK : CollarKernelContract) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {κI : ℝ} (hκI : 0 < κI) :
    ∃ (d₂ cstar : ℝ) (W₀ : ℕ), 0 < d₂ ∧ 0 < cstar ∧ ∀ p : ℝ, 0 < p → p < 1 → ∃ Cp : ℝ, 0 ≤ Cp ∧
      ∀ (P : Parameters), P.b = b → W₀ ≤ P.W → ∀ {m : ℕ} (L : Fin m → ℕ), IsCollarLayout P.n L →
      ∀ (π : Pairing) (S : Finset (Fin m)) (k : Fin m), k ∉ S → ∀ (buf : ℕ) (e : ℝ),
      e ∈ bulkInterval κI → ∀ κ : ℝ, 0 ≤ κ → ∀ D : ScsWardData P L 0 π S k e buf κ,
      ∀ {Cg A M ε₁ r : ℝ}, 0 ≤ Cg → 0 ≤ A → 0 ≤ ε₁ → 1 < r →
        ∫⁻ ω, ENNReal.ofReal (max 0 (conductance (scsResponse P L 0 π S k b e buf 0 ω)) ^ 2)
          ∂(ringCoordLaw P.n P.W P.b) ≤ ENNReal.ofReal Cg →
        ∫⁻ ω, ENNReal.ofReal (scsSigmaBound p (boundaryZ b e).im κ (D.Q (oldCoords L 0 k ω)) +
            scsSigmaBound p (boundaryZ b e).im κ (D.Q (oldCoords L 0 k ω)) ^ 2)
          ∂(ringCoordLaw P.n P.W P.b) ≤ ENNReal.ofReal A →
        eLpNorm (scsStageLogDiff P L π S k e buf κ) (ENNReal.ofReal r)
          (ringCoordLaw P.n P.W P.b) ≤ ENNReal.ofReal M →
        (ringCoordLaw P.n P.W P.b)
          {ω | d₂ < matchedDistance b e (oldX0 L 0 π S k b e buf ω)} ≤ ENNReal.ofReal ε₁ →
        ∫⁻ ω, ENNReal.ofReal |scsStageLogDiff P L π S k e buf κ ω| ∂(ringCoordLaw P.n P.W P.b) ≤
          ENNReal.ofReal Cp * (ENNReal.ofReal A + ENNReal.ofReal (Real.sqrt Cg * Real.sqrt A)) +
            ENNReal.ofReal M * ENNReal.ofReal (ε₁ + A / (cstar * P.W)) ^ (1 - 1 / r) := by
  obtain ⟨d₂, cstar, W₀, hd₂, hc, hB⟩ := scs_collar_log_bound hK hb0 hb1 hκI
  refine ⟨d₂, cstar, max W₀ 1, hd₂, hc, fun p hp0 hp1 => ?_⟩
  obtain ⟨Cp, hCp, hmain⟩ := hB p hp0 hp1
  refine ⟨Cp, hCp, ?_⟩
  intro P hPb hW m L hL π S k hk buf e he κ hκ D Cg A M ε₁ r hCg hA hε₁ hr hg2 hσ2 hDr hcert
  subst hPb
  have he1 : -2 < e := by have := he.1; linarith
  have he2 : e < 2 := by have := he.2; linarith
  have hη : 0 < (boundaryZ P.b e).im := boundaryZ_im_pos (by linarith [P.b_lt_half]) he1 he2
  set μ := ringCoordLaw P.n P.W P.b
  set O := oldCoords (W := P.W) L (0 : ZMod P.n) k
  set Uc := toCriticalCollar ∘ freshCollar (W := P.W) L (0 : ZMod P.n) k
  have hO : Measurable O := measurable_oldCoords L (0 : ZMod P.n) k
  have hU : Measurable Uc :=
    (scs_measurable_toCriticalCollar P.W).comp (measurable_freshCollar L (0 : ZMod P.n) k)
  have hind : IndepFun Uc O μ :=
    (indepFun_freshCollar_oldCoords (L := L) (s := (0 : ZMod P.n)) k P.b).comp
      (scs_measurable_toCriticalCollar P.W) measurable_id
  have hlaw : μ.map Uc = BlockBand.Internal.Contracts.Critical.collarLaw P.W P.b :=
    (hasLaw_toCriticalCollar hL k P.b).map_eq
  set σb : (oldCoordSet L 0 k → Matrix (Fin P.W) (Fin P.W) ℂ) → ℝ :=
    fun o => scsSigmaBound p (boundaryZ P.b e).im κ (D.Q o)
  have hσm : Measurable σb := by
    have hQH : ∀ o, (D.Q o).IsHermitian := fun o => (D.posSemidef_Q o).isHermitian
    have h1 := rh_measurable_fracTrace D.measurable_Q hQH hp0
    have h2 := rh_measurable_fracTrace D.measurable_Q hQH (by positivity : 0 < p / 2)
    exact measurable_const.mul (measurable_const.mul
      ((measurable_const.mul h1).add (measurable_const.mul h2)))
  have hσle : ∀ o, scsSigma p (D.S₀ o) (D.S₁ o) ≤ σb o := fun o =>
    sc_source_unitary_dilation (D.unitary o) (D.posSemidef_Q o) hη.le hκ hp0 (by linarith)
      (D.ward_diff o p hp0 (by linarith)) (D.contraction o) (D.ward_defect o)
  have hdm : Measurable fun o => scatteringDistance P.b e (D.S₀ o).toBlocks₁₁ :=
    (scs_continuous_scatteringDistance P.b e P.W).measurable.comp
      (scs_measurable_toBlocks11.comp D.measurable_S₀)
  -- the stage difference is the collar difference almost surely
  have hae : (fun ω => scsStageLogDiff P L π S k e buf κ ω) =ᵐ[μ]
      fun ω => scsCollarLogDiff P.b e (Uc ω) (D.S₀ (O ω)) (D.S₁ (O ω)) := by
    filter_upwards [scs_stageLog_sub_ae P L 0 hL hk π he1 he2 buf hκ, D.block₀, D.block₁]
      with ω h h0 h1
    simp only [scsStageLogDiff, scsCollarLogDiff, Function.comp_apply, O, Uc, h0, h1]
    exact h
  have hg2' : ∫⁻ ω, ENNReal.ofReal (max 0 (conductance (D.S₀ (O ω)).toBlocks₁₁) ^ 2) ∂μ ≤
      ENNReal.ofReal Cg := by
    refine le_of_eq_of_le (lintegral_congr_ae ?_) hg2
    filter_upwards [D.block₀] with ω h0
    simp only [O, h0]
  have hDr' : eLpNorm (fun ω => scsCollarLogDiff P.b e (Uc ω) (D.S₀ (O ω)) (D.S₁ (O ω)))
      (ENNReal.ofReal r) μ ≤ ENNReal.ofReal M := by
    rw [← eLpNorm_congr_ae hae]; exact hDr
  have hcert' : μ {ω | d₂ < scatteringDistance P.b e (D.S₀ (O ω)).toBlocks₁₁} ≤
      ENNReal.ofReal ε₁ := by
    refine le_trans (measure_mono_ae ?_) hcert
    filter_upwards [D.block₀] with ω h0 hω
    simp only [O, h0, scs_scatteringDistance_oldScattering hη] at hω ⊢
    exact hω
  have hmain' := hmain P.W P.W_pos (le_trans (le_max_left _ _) hW) e he μ D.β Uc O hU hO hind
    hlaw D.S₀ D.S₁ σb D.measurable_S₀ D.measurable_S₁ hσm D.unitary D.contraction hσle hdm
    hCg hA hε₁ hr hg2' hσ2 hDr' hcert'
  refine le_of_eq_of_le (lintegral_congr_ae ?_) hmain'
  filter_upwards [hae] with ω h
  rw [h]

end BlockBand.Endpoints
