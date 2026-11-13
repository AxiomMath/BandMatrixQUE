module

public import BlockBand.Endpoints.Normalization.LeadProfileAssemblyFinal
public import BlockBand.Endpoints.Normalization.LeadProfileCommonPortMeasurable
public import BlockBand.Endpoints.Clock.SmallBall
public import BlockBand.Layers.PathGrowth
public import BlockBand.Layers.LayerMeasurability

/-!
# The physical lead-profile theorem: the regularity statement `LeadSideMeasurability`

We prove `leadSideMeasurability_holds : LeadSideMeasurability`: for every
`p` and every `Φ ∈ C_b(𝒫(𝕋))`, the energy maps `e ↦ leadLeadSide p Φ e` and
`e ↦ gaussianLeadSide p Φ e` are Borel measurable on `ℝ`.

**Proof.** The matched-lead profile `leadProfile b e n W ω h J` is the profile of the
position-mass vector `leadPositionMass b e W (n-3) ω h` (`rfl`); the profile map is measurable
(`LeadProfileCommonPort.measurable_profileOf`; the lemmas there are at fixed energy, and the
energy-joint versions are proved here). The position masses are jointly measurable in `(e, ω, h)`, since `fullInverse` is the
(Borel, totalized) matrix inverse of a matrix depending continuously on `(e, z_∂(e), ω)` with
`e ↦ z_∂(e)` measurable. On the Gaussian side, the old self-energy `leadSchur e W r ω` and the
transported probe `L(A,B; X) g` are jointly measurable in `(e, ω, A, B, g)` by the same argument
(layer matrix continuous in `(e, z₀(e), X, A, B)`). The integrand is bounded and jointly
measurable; the parametric integral against the (probability, hence s-finite) laws
`growthPathLaw ⊗ CN(0, I_{2W})` and `leadGaussianLaw` is measurable
(`StronglyMeasurable.integral_prod_right'`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal Matrix BoundedContinuousFunction

namespace LeadProfileRegularity

/-- Finite complex matrices are second countable (local instance). -/
private theorem secondCountable_matrix (m n : Type*) [Fintype m] [Fintype n] :
    SecondCountableTopology (Matrix m n ℂ) :=
  inferInstanceAs (SecondCountableTopology (m → n → ℂ))

attribute [local instance] secondCountable_matrix

/-!
## Scalar parameters
-/

theorem continuous_matchedA : Continuous matchedA := by
  have h : matchedA = fun E : ℝ =>
      ((-E / 2 : ℝ) : ℂ) + ((-Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I := by
    funext E
    apply Complex.ext <;> simp [matchedA]
  rw [h]
  fun_prop

theorem measurable_boundaryZ (b : ℝ) : Measurable (fun e : ℝ => boundaryZ b e) := by
  unfold boundaryZ
  exact continuous_matchedA.measurable.inv.add
    (measurable_const.mul continuous_matchedA.measurable)

theorem measurable_commonZ (b : ℝ) : Measurable (fun e : ℝ => commonZ b e) := by
  unfold commonZ
  exact continuous_matchedA.measurable.inv.add
    (measurable_const.mul continuous_matchedA.measurable)

/-!
## The matched-lead side
-/

/-- `G(e, ω) = 𝓜(e, ω)⁻¹` is jointly measurable. -/
theorem measurable_fullInverse_joint (b : ℝ) (W r : ℕ) :
    Measurable (fun q : ℝ × GrowthPath W => fullInverse b q.1 W r q.2) := by
  have h1 : Continuous (fun ω : GrowthPath W => pathMatrix (pathAt W r ω)) :=
    (BlockBand.Endpoints.Clock.continuous_pathMatrix W r).comp
      (BlockBand.Endpoints.Clock.continuous_pathAt W r)
  have h2 : Continuous (fun ω : GrowthPath W => pathPortCoupling (pathAt W r ω)) :=
    (BlockBand.Endpoints.Clock.continuous_pathPortCoupling W r).comp
      (BlockBand.Endpoints.Clock.continuous_pathAt W r)
  have ha : Continuous (fun q : (ℂ × ℂ) × GrowthPath W => pathMatrix (pathAt W r q.2) -
      q.1.1 • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)) :=
    (h1.comp continuous_snd).sub ((continuous_fst.comp continuous_fst).smul continuous_const)
  have hd : Continuous (fun q : (ℂ × ℂ) × GrowthPath W =>
      q.1.2 • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) :=
    (continuous_snd.comp continuous_fst).smul continuous_const
  have hb : Continuous (fun q : (ℂ × ℂ) × GrowthPath W => pathPortCoupling (pathAt W r q.2)) :=
    h2.comp continuous_snd
  have hc : Continuous (fun q : (ℂ × ℂ) × GrowthPath W =>
      Matrix.fromBlocks (pathMatrix (pathAt W r q.2) -
          q.1.1 • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ))
        (pathPortCoupling (pathAt W r q.2)) (pathPortCoupling (pathAt W r q.2))ᴴ
        (q.1.2 • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))) :=
    Continuous.matrix_fromBlocks ha hb hb.matrix_conjTranspose hd
  have hg : Measurable (fun q : ℝ × GrowthPath W => (((q.1 : ℂ), boundaryZ b q.1), q.2)) :=
    ((Complex.measurable_ofReal.comp measurable_fst).prodMk
      ((measurable_boundaryZ b).comp measurable_fst)).prodMk measurable_snd
  have hm := hc.measurable.comp hg
  have hi := BlockBand.Layers.measurable_matrix_inv.comp hm
  exact hi

/-- The position masses are jointly measurable in `(e, ω, h)`. -/
theorem measurable_leadPositionMass_joint (b : ℝ) (W r : ℕ) :
    Measurable (fun q : ℝ × GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      leadPositionMass b q.1 W r q.2.1 q.2.2) := by
  have hU : Measurable (fun q : ℝ × GrowthPath W => leadResponse b q.1 W r q.2) := by
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    unfold leadResponse
    exact (measurable_pi_apply (Sum.inr y)).comp ((measurable_pi_apply x).comp
      (measurable_fullInverse_joint b W r))
  have hc : Continuous (fun p : Matrix (FullSite W r) (Fin 2 × Fin W) ℂ × (Fin 2 × Fin W → ℂ) =>
      p.1 *ᵥ p.2) := Continuous.matrix_mulVec continuous_fst continuous_snd
  have hψ : Measurable (fun q : ℝ × GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      leadResponse b q.1 W r q.2.1 *ᵥ q.2.2) :=
    hc.measurable.comp ((hU.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd))
  refine measurable_pi_iff.mpr fun x => ?_
  rcases x with i | j
  · simp only [leadPositionMass]
    exact Finset.measurable_sum _ fun a _ =>
      (((measurable_pi_apply _).comp hψ).norm).pow_const 2
  · simp only [leadPositionMass]
    exact Finset.measurable_sum _ fun a _ =>
      (((measurable_pi_apply _).comp hψ).norm).pow_const 2

/-- The rotated matched-lead profile is jointly measurable in `(e, ω, h)`. -/
theorem measurable_leadProfile_eJoint (b : ℝ) (n W J : ℕ) :
    Measurable (fun q : ℝ × GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      leadProfile b q.1 n W q.2.1 q.2.2 J) :=
  (LeadProfileCommonPort.measurable_profileOf n (n - 3) J).comp
    (measurable_leadPositionMass_joint b W (n - 3))

/-!
## The Gaussian side
-/

/-- The old self-energy `X(e, ω) = leadSchur e W r ω` is jointly measurable. -/
theorem measurable_leadSchur_joint (W r : ℕ) :
    Measurable (fun q : ℝ × GrowthPath W => leadSchur q.1 W r q.2) := by
  have h1 : Continuous (fun ω : GrowthPath W => pathMatrix (pathAt W r ω)) :=
    (BlockBand.Endpoints.Clock.continuous_pathMatrix W r).comp
      (BlockBand.Endpoints.Clock.continuous_pathAt W r)
  have h2 : Continuous (fun ω : GrowthPath W => pathPortCoupling (pathAt W r ω)) :=
    (BlockBand.Endpoints.Clock.continuous_pathPortCoupling W r).comp
      (BlockBand.Endpoints.Clock.continuous_pathAt W r)
  have hc : Continuous (fun q : ℂ × GrowthPath W =>
      pathMatrix (pathAt W r q.2) - q.1 • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)) :=
    (h1.comp continuous_snd).sub (continuous_fst.smul continuous_const)
  have hg : Measurable (fun q : ℝ × GrowthPath W => ((q.1 : ℂ), q.2)) :=
    (Complex.measurable_ofReal.comp measurable_fst).prodMk measurable_snd
  have hs := hc.measurable.comp hg
  have hinv := BlockBand.Layers.measurable_matrix_inv.comp hs
  have hm : Continuous (fun x : Matrix (Fin r × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ => x.1ᴴ * x.2 * x.1) :=
    (continuous_fst.matrix_conjTranspose.matrix_mul continuous_snd).matrix_mul continuous_fst
  have hC : Measurable (fun q : ℝ × GrowthPath W => pathPortCoupling (pathAt W r q.2)) :=
    h2.measurable.comp measurable_snd
  have hall := hm.measurable.comp (hC.prodMk hinv)
  exact hall

theorem continuous_blockDiag (k W : ℕ) :
    Continuous (fun A : Fin k → Matrix (Fin W) (Fin W) ℂ => BlockBand.Internal.Contracts.Layers.blockDiag A) := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  unfold BlockBand.Internal.Contracts.Layers.blockDiag
  split_ifs
  · exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply _))
  · exact continuous_const

theorem continuous_bondMatrix (W : ℕ) (σ : LayerShape) :
    Continuous (fun B : Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ =>
      bondMatrix σ B) := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  unfold bondMatrix
  split_ifs
  · exact (continuous_apply _).comp ((continuous_apply _).comp ((continuous_apply _).comp
      (continuous_apply _)))
  · exact continuous_const

/-- `(e, X, A, B) ↦ 𝒢⁻¹ = layerMatrix σ e z(e) X (A, B)` is jointly measurable for a measurable
`z(e)`. -/
theorem measurable_layerMatrix_joint (W : ℕ) (σ : LayerShape) {z : ℝ → ℂ} (hz : Measurable z) :
    Measurable (fun q : ℝ × Matrix (PhysSite W σ) (PhysSite W σ) ℂ × LayerSample W σ =>
      layerMatrix σ q.1 (z q.1) q.2.1 q.2.2) := by
  have hc : Continuous (fun q : (ℂ × ℂ) × Matrix (PhysSite W σ) (PhysSite W σ) ℂ ×
      LayerSample W σ =>
      Matrix.fromBlocks (BlockBand.Internal.Contracts.Layers.blockDiag q.2.2.1 - q.1.1 • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
          - q.2.1) (bondMatrix σ q.2.2.2) (bondMatrix σ q.2.2.2)ᴴ
        (q.1.2 • (1 : Matrix (PortSite W σ) (PortSite W σ) ℂ))) := by
    have hA : Continuous (fun q : (ℂ × ℂ) × Matrix (PhysSite W σ) (PhysSite W σ) ℂ ×
        LayerSample W σ => BlockBand.Internal.Contracts.Layers.blockDiag q.2.2.1) :=
      (continuous_blockDiag σ.blocks W).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))
    have hB : Continuous (fun q : (ℂ × ℂ) × Matrix (PhysSite W σ) (PhysSite W σ) ℂ ×
        LayerSample W σ => bondMatrix σ q.2.2.2) :=
      (continuous_bondMatrix W σ).comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd))
    have hX : Continuous (fun q : (ℂ × ℂ) × Matrix (PhysSite W σ) (PhysSite W σ) ℂ ×
        LayerSample W σ => q.2.1) := continuous_fst.comp continuous_snd
    have hs : Continuous (fun q : (ℂ × ℂ) × Matrix (PhysSite W σ) (PhysSite W σ) ℂ ×
        LayerSample W σ => q.1.1 • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)) :=
      (continuous_fst.comp continuous_fst).smul continuous_const
    have hz : Continuous (fun q : (ℂ × ℂ) × Matrix (PhysSite W σ) (PhysSite W σ) ℂ ×
        LayerSample W σ => q.1.2 • (1 : Matrix (PortSite W σ) (PortSite W σ) ℂ)) :=
      (continuous_snd.comp continuous_fst).smul continuous_const
    exact Continuous.matrix_fromBlocks ((hA.sub hs).sub hX) hB hB.matrix_conjTranspose hz
  have hg : Measurable (fun q : ℝ × Matrix (PhysSite W σ) (PhysSite W σ) ℂ × LayerSample W σ =>
      (((q.1 : ℂ), z q.1), q.2)) :=
    ((Complex.measurable_ofReal.comp measurable_fst).prodMk (hz.comp measurable_fst)).prodMk
      measurable_snd
  have hall := hc.measurable.comp hg
  exact hall

/-- `(e, X, A, B) ↦ L(A, B; X)` at energy `e` is jointly measurable. -/
theorem measurable_commonPortL_eJoint (b : ℝ) (W : ℕ) :
    Measurable (fun q : ℝ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × LayerSample W .common =>
      commonPortL b q.1 q.2.1 q.2.2) := by
  have hG : Measurable (fun q : ℝ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      LayerSample W .common => commonPortResolvent b q.1 q.2.1 q.2.2) :=
    BlockBand.Layers.measurable_matrix_inv.comp
      (measurable_layerMatrix_joint W .common (measurable_commonZ b))
  have hK : Measurable (fun q : ℝ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      LayerSample W .common => matchedLeadK b q.1 q.2.1) := by
    have hc : Continuous (fun x : ℂ × Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
        x.1 • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - x.2) :=
      (continuous_fst.smul continuous_const).sub continuous_snd
    exact hc.measurable.comp (((measurable_boundaryZ b).comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd))
  have hm : Continuous (fun x : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (LayerSite W .common) (LayerSite W .common) ℂ => x.1 * x.2.toBlocks₁₂) := by
    have h : Continuous (fun G : Matrix (LayerSite W .common) (LayerSite W .common) ℂ =>
        G.toBlocks₁₂) :=
      continuous_pi fun x => continuous_pi fun y => by unfold Matrix.toBlocks₁₂; fun_prop
    exact continuous_fst.matrix_mul (h.comp continuous_snd)
  unfold commonPortL
  exact hm.measurable.comp (hK.prodMk hG)

/-- The transported probe `L g` at the old self-energy `X(e, ω)` is jointly measurable in
`(e, ω, A, B, g)`. -/
theorem measurable_commonPortProbe_eJoint (b : ℝ) (W r : ℕ) :
    Measurable (fun q : ℝ × ((GrowthPath W × LayerSample W .common) × (Fin 1 × Fin W → ℂ)) =>
      commonPortProbe b q.1 (leadSchur q.1 W r q.2.1.1) (q.2.1.2, q.2.2)) := by
  have h1 : Measurable (fun q : ℝ × ((GrowthPath W × LayerSample W .common) ×
      (Fin 1 × Fin W → ℂ)) => (q.1, q.2.1.1)) :=
    measurable_fst.prodMk (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hX := (measurable_leadSchur_joint W r).comp h1
  have hl : Measurable (fun q : ℝ × ((GrowthPath W × LayerSample W .common) ×
      (Fin 1 × Fin W → ℂ)) => q.2.1.2) := measurable_snd.comp (measurable_fst.comp measurable_snd)
  have h2 := measurable_fst.prodMk (hX.prodMk hl)
  have hL := (measurable_commonPortL_eJoint b W).comp h2
  have hc : Continuous (fun p : Matrix (Fin 2 × Fin W) (Fin 1 × Fin W) ℂ × (Fin 1 × Fin W → ℂ) =>
      p.1 *ᵥ p.2) := Continuous.matrix_mulVec continuous_fst continuous_snd
  have hg : Measurable (fun q : ℝ × ((GrowthPath W × LayerSample W .common) ×
      (Fin 1 × Fin W → ℂ)) => q.2.2) := measurable_snd.comp measurable_snd
  have hall := hc.measurable.comp (hL.prodMk hg)
  exact hall

end LeadProfileRegularity

open LeadProfileRegularity

/-- `e ↦ leadLeadSide p Φ e` is measurable.
Interface of the proof of
.
-/
theorem measurable_leadLeadSide (p : Parameters) (Φ : MassProfile →ᵇ ℝ) :
    Measurable (leadLeadSide p Φ) := by
  have hF : Measurable (fun q : ℝ × (GrowthPath p.W × (Fin 2 × Fin p.W → ℂ)) =>
      (p.n : ℝ)⁻¹ * ∑ J ∈ Finset.range p.n, Φ (leadProfile p.b q.1 p.n p.W q.2.1 q.2.2 J)) :=
    measurable_const.mul (Finset.measurable_sum _ fun J _ =>
      (measurable_massProfile_bcf Φ).comp (measurable_leadProfile_eJoint p.b p.n p.W J))
  have : IsProbabilityMeasure (growthPathLaw p.W p.b) := by unfold growthPathLaw; infer_instance
  exact (hF.stronglyMeasurable.integral_prod_right'
    (ν := (growthPathLaw p.W p.b).prod (circularVectorLaw (Fin 2 × Fin p.W)))).measurable

/-- `e ↦ gaussianLeadSide p Φ e` is measurable.
Interface of the proof of
.
-/
theorem measurable_gaussianLeadSide (p : Parameters) (Φ : MassProfile →ᵇ ℝ) :
    Measurable (gaussianLeadSide p Φ) := by
  have hP := measurable_commonPortProbe_eJoint p.b p.W (p.n - 3)
  have hω : Measurable (fun q : ℝ × ((GrowthPath p.W × LayerSample p.W .common) ×
      (Fin 1 × Fin p.W → ℂ)) => q.2.1.1) := measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hq := measurable_fst.prodMk (hω.prodMk hP)
  have hF : Measurable (fun q : ℝ × ((GrowthPath p.W × LayerSample p.W .common) ×
      (Fin 1 × Fin p.W → ℂ)) =>
      (p.n : ℝ)⁻¹ * ∑ J ∈ Finset.range p.n, Φ (leadProfile p.b q.1 p.n p.W q.2.1.1
        (commonPortProbe p.b q.1 (leadSchur q.1 p.W (p.n - 3) q.2.1.1) (q.2.1.2, q.2.2)) J)) := by
    refine measurable_const.mul (Finset.measurable_sum _ fun J _ => ?_)
    have h := (measurable_massProfile_bcf Φ).comp ((measurable_leadProfile_eJoint p.b p.n p.W J).comp hq)
    exact h
  have : IsProbabilityMeasure (growthPathLaw p.W p.b) := by unfold growthPathLaw; infer_instance
  have : IsProbabilityMeasure (leadGaussianLaw p) := by unfold leadGaussianLaw; infer_instance
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := leadGaussianLaw p)).measurable

/-- **`LeadSideMeasurability`**: both lead sides are measurable in the energy, for every `p` and
`Φ`. -/
theorem leadSideMeasurability_holds : LeadSideMeasurability :=
  fun p Φ => ⟨measurable_leadLeadSide p Φ, measurable_gaussianLeadSide p Φ⟩

end BlockBand.Endpoints.Normalization
