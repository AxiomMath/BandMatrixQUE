module

public import BlockBand.Critical.MatrixClosing.Poles.Conditional

/-!
# Matrix closing, poles clause: identification and averaging over `(A, B)`

The conditional convergence of the collar poles is uniform, so it remains valid after averaging over
`A, B`.

*Law.* `collarLaw W b = layerLaw W b .common ⊗ GUE(PortSite)(c/W)`, `c = 1 - 2b`.

* `collarF e X ω₁ = portSchurFin e X (ω₁, 0)` (`F = -e - B^*D⁻¹B` on `Fin W`) and
  `portSchurFin_eq_add`: `Q = F + reindex G`.
* `collarVt b e X J ω₁ = (π w/W)^{1/2}(J^*KD⁻¹B)^*`, `w = residueWeight = Wρ(e)/η` in the bulk.
* `collarResidue_eq_markRes`, **`atomSum_collarFunction_eq`**: the poles and residues of
  `collarFunction` are `markAtoms ρ(e) 0 Ṽ (F + reindex G)`.
* `integral_port_eq`: the inner `G`-average is the `GUE_W(c/W)` average over `Fin W`.
* `CollarGood`, **`CollarGoodEventAt r`**: the good event of the conditional collar and the
  statement that it has asymptotically full probability (regularity of `F`, admissibility of the
  weighted frame, and the density scale).
* **`collarPolesLaplaceAt_of_goodEvent : RelativeMixedVectorsDecorated → 0 < r →
  CollarGoodEventAt r → CollarPolesLaplaceAt r`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.RelativeVectors
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Herglotz BlockBand.Critical.WeightedDensity
open scoped ComplexConjugate ComplexOrder

variable {W r : ℕ}

/-!
## The conditional deformation and the weighted frame
-/

/-- The conditional deformation `F = -e - B^*D⁻¹B` on `Fin W`, a function of `(A, B)` only. -/
def collarF (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω₁ : LayerSample W .common) :
    Matrix (Fin W) (Fin W) ℂ :=
  portSchurFin e X (ω₁, 0)

theorem portSchurFin_eq_add (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω₁ : LayerSample W .common) (G : Matrix (PortSite W .common) (PortSite W .common) ℂ) :
    portSchurFin e X (ω₁, G) =
      collarF e X ω₁ + Matrix.reindex (portEquiv W) (portEquiv W) G := by
  have h : portSchur e X (ω₁, G) = portSchur e X (ω₁, 0) + G := by
    simp only [portSchur, topBlock]; abel
  rw [collarF, portSchurFin, portSchurFin, h]
  simp [Matrix.reindex_apply, Matrix.submatrix_add]

/-- The weighted frame `Ṽ = (πρ(e)/η)^{1/2}(J^*KD⁻¹B)^*` on `Fin W`. The paper's
`Ṽ = -(πρ(e))^{1/2}V` carries a sign; this definition has none. The sign is immaterial: only
`ṼṼ^*`-quadratic quantities (residues and `Ṽ^*Γ_FṼ`) enter.
-/
def collarVt (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω₁ : LayerSample W .common) :
    Matrix (Fin W) (Fin r) ℂ :=
  ((Real.sqrt (Real.pi * residueWeight W b e / W) : ℝ) : ℂ) • (frameFin b e X J (ω₁, 0))ᴴ

theorem residueWeight_nonneg (W : ℕ) (b e : ℝ) : 0 ≤ residueWeight W b e := le_max_right _ _

theorem mul_vecMulVec_conjTranspose {m n : Type*} [Fintype n] (M : Matrix m n ℂ)
    (u : n → ℂ) : M * vecMulVec u (star u) * Mᴴ = vecMulVec (M *ᵥ u) (star (M *ᵥ u)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- **The collar residues are the canonical residues of the weighted marks**:
`(Wρ/η)(J^*KD⁻¹B)u_ℓu_ℓ^*(J^*KD⁻¹B)^* = π⁻¹(√W Ṽ^*u_ℓ)(√W Ṽ^*u_ℓ)^*`. -/
theorem collarResidue_eq_markRes (hW : 0 < W) (b e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ)
    (ω₁ : LayerSample W .common) (G : Matrix (PortSite W .common) (PortSite W .common) ℂ)
    (ℓ : Fin W) :
    collarResidue b e X J (ω₁, G) ℓ =
      markRes (collarVt b e X J ω₁) (portSchurFin e X (ω₁, G)) ℓ := by
  set w := residueWeight W b e
  set s := Real.sqrt (Real.pi * w / W)
  set M := frameFin b e X J (ω₁, G)
  set u := freshEigenvector (portSchurFin e X (ω₁, G)) ℓ
  have hM : frameFin b e X J (ω₁, 0) = M := rfl
  have hw : 0 ≤ w := residueWeight_nonneg W b e
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hs2 : s ^ 2 = Real.pi * w / W := Real.sq_sqrt (by positivity)
  have hW2 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hWr.le
  have hkey : ((Real.pi : ℂ)⁻¹ * ((Real.sqrt W * s : ℝ) : ℂ) * ((Real.sqrt W * s : ℝ) : ℂ)) =
      (w : ℂ) := by
    have : Real.pi⁻¹ * (Real.sqrt W * s) * (Real.sqrt W * s) = w := by
      have e1 : Real.pi⁻¹ * (Real.sqrt W * s) * (Real.sqrt W * s) =
          Real.pi⁻¹ * (Real.sqrt W ^ 2 * s ^ 2) := by ring
      rw [e1, hW2, hs2]; field_simp
    rw [← this]; push_cast; ring
  have hmv : markVec (collarVt b e X J ω₁) (portSchurFin e X (ω₁, G)) ℓ =
      ((Real.sqrt W * s : ℝ) : ℂ) • (M *ᵥ u) := by
    unfold markVec collarVt
    rw [hM, conjTranspose_smul, conjTranspose_conjTranspose, Complex.star_def,
      Complex.conj_ofReal, Matrix.smul_mulVec, smul_smul]
    push_cast; rfl
  unfold collarResidue markRes
  rw [hmv, BlockBand.Coarea.FreshPalm.freshProjector, mul_vecMulVec_conjTranspose]
  ext i j
  rw [canonicalResidue_apply]
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul,
    map_mul, Complex.conj_ofReal]
  rw [← hkey]
  simp only [Complex.star_def]
  ring

theorem atomSum_ofAtoms_congr {n : ℕ} (C0 C1 : Matrix (Fin r) (Fin r) ℂ) (h0 : C0.IsHermitian)
    (h1 : C1.IsHermitian) {pts pts' : Fin n → ℝ} {res res' : Fin n → Matrix (Fin r) (Fin r) ℂ}
    (hres : ∀ ℓ, (res ℓ).PosSemidef) (hres' : ∀ ℓ, (res' ℓ).PosSemidef) (hp : pts = pts')
    (hr : res = res') (f : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    (ofAtoms C0 h0 pts res hres).atomSum f = (ofAtoms C1 h1 pts' res' hres').atomSum f := by
  subst hp hr; rfl

/-- **The collar poles are the marked atoms of `F + G`** at scale `ρ(e)`, energy `0`, frame
`Ṽ`. -/
theorem atomSum_collarFunction_eq (hW : 0 < W) (b e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ)
    (ω₁ : LayerSample W .common) (G : Matrix (PortSite W .common) (PortSite W .common) ℂ)
    (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    (collarFunction b e X J (ω₁, G)).atomSum φ =
      (markAtoms (Parameters.semicircleDensity e) 0 (collarVt b e X J ω₁)
        (collarF e X ω₁ + Matrix.reindex (portEquiv W) (portEquiv W) G)).atomSum φ := by
  rw [← portSchurFin_eq_add]
  unfold collarFunction markAtoms
  refine atomSum_ofAtoms_congr _ _ _ _ (collarResidue_posSemidef b e X J (ω₁, G))
    (markRes_posSemidef _ _) ?_ ?_ φ
  · funext ℓ; simp [markPts, poleScale, mul_assoc]
  · funext ℓ; exact collarResidue_eq_markRes hW b e X J ω₁ G ℓ

/-!
## Averaging over `(A, B)`
-/

/-- The inner `G`-average of the collar Laplace integrand is the decorated functional of the marked
atoms of `F + G'`, `G' ~ GUE_W(c/W)` on `Fin W`. -/
theorem integral_port_eq (hW : 0 < W) (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω₁ : LayerSample W .common)
    (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) (t : NNReal) :
    ∫ G, Real.exp (-(collarFunction b e X J (ω₁, G)).atomSum φ) ∂gueMeasure (PortSite W .common) t =
      ∫ G', Real.exp (-(markAtoms (Parameters.semicircleDensity e) 0 (collarVt b e X J ω₁)
        (collarF e X ω₁ + G')).atomSum φ) ∂gueMeasure (Fin W) t := by
  have hR : Measurable (Matrix.reindex (portEquiv W) (portEquiv W) :
      Matrix (PortSite W .common) (PortSite W .common) ℂ → Matrix (Fin W) (Fin W) ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hm : Measurable fun G' => Real.exp (-(markAtoms (Parameters.semicircleDensity e) 0
      (collarVt b e X J ω₁) (collarF e X ω₁ + G')).atomSum φ) :=
    (measurable_exp_atomSum_markAtoms (Parameters.semicircleDensity e) 0
      (collarVt b e X J ω₁) φ).comp (measurable_const_add (collarF e X ω₁))
  rw [← BlockBand.Coarea.GUELaw.gueMeasure_map_reindex (portEquiv W) t,
    integral_map hR.aemeasurable hm.aestronglyMeasurable]
  simp_rw [atomSum_collarFunction_eq hW]

/-- **The good event of the conditional collar** at precision `ε`: `F = -e - B^*D⁻¹B` is in the
fresh class at `(c, 0)`, `c = 1 - 2b`; the weighted frame `Ṽ` is admissible,
`|(Ṽ^*Γ_FṼ - I)_{ij}| ≤ ε` (the collar projection covariance); and `|ρ(e) - ρ_F| ≤ ε`. -/
def CollarGood (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (A r₀ s₀ v₀ ε : ℝ) (ω₁ : LayerSample W .common) :
    Prop :=
  FreshClass (collarF e X ω₁) A (1 - 2 * b) 0 r₀ s₀ v₀ ∧
    (∀ i j : Fin r, ‖((collarVt b e X J ω₁)ᴴ * freshGamma (collarF e X ω₁) (1 - 2 * b) 0 *
      collarVt b e X J ω₁ - (1 : Matrix (Fin r) (Fin r) ℂ)) i j‖ ≤ ε) ∧
    |Parameters.semicircleDensity e - unfoldingDensity (collarF e X ω₁) (1 - 2 * b) 0| ≤ ε

/-- **The good event at rank `r`**: along every admissible old sequence there are fresh
constants `A, r₀, s₀, v₀` for `c = 1 - 2b` such that for every `ε > 0` the `(A, B)`-probability of
the complement of `CollarGood ε` tends to `0` (outer measure). This covers the regularity of `F`
with arbitrarily small exceptional probability, the collar projection covariance, and
`r_{F,c}(0) = ρ(E) + o(1)`; it is the part of hypothesis 1 stated here as a hypothesis. -/
def CollarGoodEventAt (r : ℕ) : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ S : OldSequence b κ r,
    ∃ A r₀ s₀ v₀ : ℝ, FreshConstants (1 - 2 * b) r₀ s₀ v₀ ∧ ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => layerLaw (S.W N) b .common
        {ω₁ | ¬ CollarGood b (S.e N) (S.X N) (S.J N) A r₀ s₀ v₀ ε ω₁}) atTop (𝓝 0)

/-- **Hypothesis 1 at a positive rank from the decorated clause of the relative mixed vectors
theorem and the good event.** For fixed `(A, B)` in the good event the
`G`-average is within `δ/2` of the limit (`conditional_laplace`, uniformly); the bad event has
vanishing probability; Fubini over `collarLaw = layerLaw ⊗ GUE`. -/
theorem collarPolesLaplaceAt_of_goodEvent (hD : RelativeMixedVectorsDecorated) (hr : 0 < r)
    (hG : CollarGoodEventAt r) : CollarPolesLaplaceAt r := by
  intro b hb0 hb κ hκ S φ hφ
  obtain ⟨A, r₀, s₀, v₀, hFC, hbad⟩ := hG b hb0 hb κ hκ S
  have hDC := decoratedContinuous_of_decorated hD
  set L := decoratedSineLaplace r (canonTest φ)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨ε, hε, N₀, hcond⟩ := conditional_laplace hDC hFC hr φ hφ (δ := δ / 2) (by linarith)
  set C := 1 + |L|
  have hC : 0 < C := by positivity
  have hq : 0 < δ / (4 * C) := by positivity
  have hb1 := (ENNReal.tendsto_nhds_zero.1 (hbad ε hε)) (ENNReal.ofReal (δ / (4 * C)))
    (ENNReal.ofReal_pos.2 hq)
  have hW := S.tendsto_W.eventually_ge_atTop N₀
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hb1.and hW)
  refine ⟨M, fun N hN => ?_⟩
  obtain ⟨hμ, hWN⟩ := hM N hN
  rw [Real.dist_eq]
  have hWpos := S.W_pos N
  set μ := layerLaw (S.W N) b .common
  have := BlockBand.Layers.bond_isProbabilityMeasure_layerLaw (S.W N) b .common
  set t := Real.toNNReal ((1 - 2 * b) / (S.W N))
  set Φ : CollarSample (S.W N) → ℝ := fun ω => Real.exp (-(S.collarFns N ω).atomSum φ)
  have hΦm : Measurable Φ := Real.measurable_exp.comp
    (measurable_atomSum_collarFunction b (S.e N) (S.X N) (S.J N) φ).neg
  have hΦ01 : ∀ ω, 0 ≤ Φ ω ∧ Φ ω ≤ 1 := fun ω =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (neg_nonpos.2 (atomSum_nonneg _ hφ))⟩
  have hΦi : Integrable Φ (collarLaw (S.W N) b) :=
    Integrable.of_bound hΦm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hΦ01 ω).1]; exact (hΦ01 ω).2)
  set g : LayerSample (S.W N) .common → ℝ := fun ω₁ => ∫ G, Φ (ω₁, G) ∂gueMeasure _ t
  have hFub : ∫ ω, Φ ω ∂collarLaw (S.W N) b = ∫ ω₁, g ω₁ ∂μ := integral_prod Φ hΦi
  have hgm : Measurable g :=
    (hΦm.stronglyMeasurable.integral_prod_right' (ν := gueMeasure _ t)).measurable
  have hg01 : ∀ ω₁, 0 ≤ g ω₁ ∧ g ω₁ ≤ 1 := by
    intro ω₁
    refine ⟨integral_nonneg fun G => (hΦ01 _).1, ?_⟩
    calc g ω₁ ≤ ∫ _G, (1 : ℝ) ∂gueMeasure (PortSite (S.W N) .common) t :=
          integral_mono_of_nonneg (Eventually.of_forall fun G => (hΦ01 _).1)
            (integrable_const 1) (Eventually.of_forall fun G => (hΦ01 _).2)
      _ = 1 := by simp
  have hgood : ∀ ω₁, CollarGood b (S.e N) (S.X N) (S.J N) A r₀ s₀ v₀ ε ω₁ →
      |g ω₁ - L| ≤ δ / 2 := by
    intro ω₁ h
    have e1 : g ω₁ = ∫ G', Real.exp (-(markAtoms (Parameters.semicircleDensity (S.e N)) 0
        (collarVt b (S.e N) (S.X N) (S.J N) ω₁) (collarF (S.e N) (S.X N) ω₁ + G')).atomSum φ)
          ∂gueMeasure (Fin (S.W N)) t :=
      integral_port_eq hWpos b (S.e N) (S.X N) (S.J N) ω₁ φ t
    rw [e1]
    exact hcond (S.W N) hWN _ 0 h.1 _ h.2.1 _ h.2.2
  set Bad := {ω₁ | ¬ CollarGood b (S.e N) (S.X N) (S.J N) A r₀ s₀ v₀ ε ω₁}
  set T := toMeasurable μ Bad
  have hTm : MeasurableSet T := measurableSet_toMeasurable μ Bad
  have hpt : ∀ ω₁, |g ω₁ - L| ≤ δ / 2 + C * T.indicator (fun _ => (1 : ℝ)) ω₁ := by
    intro ω₁
    by_cases hω : ω₁ ∈ T
    · rw [Set.indicator_of_mem hω, mul_one]
      have : |g ω₁ - L| ≤ 1 + |L| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (hg01 ω₁).1]
        linarith [(hg01 ω₁).2]
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      refine hgood ω₁ ?_
      by_contra hc
      exact hω (subset_toMeasurable μ Bad hc)
  have hint1 : Integrable (fun ω₁ => g ω₁ - L) μ :=
    Integrable.of_bound (hgm.sub measurable_const).aestronglyMeasurable C
      (Eventually.of_forall fun ω₁ => by
        rw [Real.norm_eq_abs]
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (hg01 ω₁).1]
        linarith [(hg01 ω₁).2])
  have hint2 : Integrable (fun ω₁ => δ / 2 + C * T.indicator (fun _ => (1 : ℝ)) ω₁) μ :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator hTm |>.const_mul C)
  have hTreal : μ.real T ≤ δ / (4 * C) := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hq.le hμ
  have hI : ∫ ω₁, (δ / 2 + C * T.indicator (fun _ => (1 : ℝ)) ω₁) ∂μ = δ / 2 + C * μ.real T := by
    rw [integral_add (integrable_const _) ((integrable_const (1 : ℝ)).indicator hTm |>.const_mul C),
      integral_const_mul, integral_indicator hTm, setIntegral_const]
    simp
  change |∫ ω, Φ ω ∂collarLaw (S.W N) b - L| < δ
  rw [hFub]
  have hsub : ∫ ω₁, g ω₁ ∂μ - L = ∫ ω₁, (g ω₁ - L) ∂μ := by
    rw [integral_sub (Integrable.of_bound hgm.aestronglyMeasurable 1
      (Eventually.of_forall fun ω₁ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg01 ω₁).1]; exact (hg01 ω₁).2))
      (integrable_const L)]
    simp
  rw [hsub]
  calc |∫ ω₁, (g ω₁ - L) ∂μ| ≤ ∫ ω₁, |g ω₁ - L| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω₁, (δ / 2 + C * T.indicator (fun _ => (1 : ℝ)) ω₁) ∂μ :=
        integral_mono hint1.abs hint2 hpt
    _ = δ / 2 + C * μ.real T := hI
    _ ≤ δ / 2 + C * (δ / (4 * C)) := by gcongr
    _ < δ := by
        have : C * (δ / (4 * C)) = δ / 4 := by field_simp
        linarith

end BlockBand.Critical.MatrixClosing.Poles
