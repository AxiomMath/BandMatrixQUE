module

public import BlockBand.Palm.MomentFlow.BridgeIdentity
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Function.Floor

/-!
# A jointly measurable version of the conditional moments

*Measure:* `flowLaw N a`; *σ-algebra:* `𝓛 = pathSigma F a s c`; *domain:* every `N`, `F`, `a`,
`s ≤ c`, `q`, configuration `ζ`.

The sample space `FlowSample N` (continuous Wiener paths) is not shown standard Borel in Mathlib,
so the version is built from a standard Borel **code** of the sample:
`flowCode ω = (entries of ω.1, Wiener values at the dyadic times k/2ⁿ)` in `CodeSpace N`. Every
Wiener value at a real time is a limit of dyadic values (`codeWiener_flowCode`, by continuity of
every path), so every observable of the flow factors measurably through `(σ, flowCode ω)`
(`codeMatrix_flowCode`, `measurable_codeMatrix`).

* `clampedMoment ζ σ ω = clamp_{K^{|ζ|}}(mono(X(σ)(ω), ζ))` with `K = max 1 (N‖q‖²)`;
  `clampedMoment_eq` (it equals the true moment on simple spectrum, `overlap_le`).
* `pathMap` (the eigenvalue path on `[s,c]`), `comap_pathMap` (`comap pathMap = 𝓛`).
* `momentVersion ζ σ ω = ∫ g_ζ(σ, z) d condDistrib(flowCode | pathMap)(pathMap ω)`:
  `momentVersion_ae_eq` (`= E[clampedMoment ζ σ | 𝓛]` a.s. for each `σ`),
  `measurable_momentVersion` (jointly measurable for `borel ⊗ 𝓛`), `measurable_momentVersion_slice`
  (each time slice is `𝓛`-measurable), `abs_momentVersion_le` (bounded by `K^{|ζ|}` everywhere).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open scoped NNReal

variable {N : ℕ}

/-!
## The standard Borel code of a sample
-/

/-- Code of a sample: initial matrix entries and Wiener values at the dyadic times `k/2ⁿ`. -/
abbrev CodeSpace (N : ℕ) := (Fin N → Fin N → ℂ) × (((Fin N × Fin N) × Fin 2) → ℕ × ℕ → ℝ)

instance : StandardBorelSpace (CodeSpace N) :=
  haveI : StandardBorelSpace (Fin N → Fin N → ℂ) := inferInstance
  haveI : StandardBorelSpace (((Fin N × Fin N) × Fin 2) → ℕ × ℕ → ℝ) := inferInstance
  StandardBorelSpace.prod

/-- The code map. -/
def flowCode (ω : FlowSample N) : CodeSpace N :=
  (fun i j => ω.1 i j, fun q p => ω.2 q ((p.2 : ℝ≥0) / 2 ^ p.1))

theorem measurable_flowCode : Measurable (flowCode (N := N)) := by
  refine Measurable.prodMk ?_ ?_
  · exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
      (measurable_matrixEntry i j).comp measurable_fst
  · exact Measurable.of_eval fun q => Measurable.of_eval fun p =>
      (ContinuousMap.measurable_eval _).comp ((measurable_pi_apply q).comp measurable_snd)

/-- Dyadic upper approximation `⌈2ⁿ t⌉₊/2ⁿ` of `t⁺`. -/
def dyadicApprox (n : ℕ) (t : ℝ) : ℝ≥0 := (⌈2 ^ n * t⌉₊ : ℝ≥0) / 2 ^ n

theorem tendsto_dyadicApprox (t : ℝ) :
    Tendsto (fun n => dyadicApprox n t) atTop (𝓝 (Real.toNNReal t)) := by
  rw [← NNReal.tendsto_coe]
  have hlow : ∀ n : ℕ, max t 0 ≤ (dyadicApprox n t : ℝ) := by
    intro n
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    simp only [dyadicApprox, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
      NNReal.coe_ofNat]
    rw [le_div_iff₀ hp]
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right ht, zero_mul]; positivity
    · rw [max_eq_left ht, mul_comm]; exact Nat.le_ceil _
  have hup : ∀ n : ℕ, (dyadicApprox n t : ℝ) ≤ max t 0 + 1 / 2 ^ n := by
    intro n
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    simp only [dyadicApprox, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
      NNReal.coe_ofNat]
    rw [div_le_iff₀ hp, add_mul, one_div, inv_mul_cancel₀ hp.ne']
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right ht, zero_mul, zero_add]
      have : ⌈2 ^ n * t⌉₊ = 0 := Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos hp.le ht)
      rw [this]; simp
    · rw [max_eq_left ht, mul_comm t]
      exact (Nat.ceil_lt_add_one (by positivity)).le
  have hlim : Tendsto (fun n : ℕ => max t 0 + 1 / (2 : ℝ) ^ n) atTop (𝓝 (max t 0)) := by
    have : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
      simp only [one_div, ← inv_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using tendsto_const_nhds.add this
  rw [Real.coe_toNNReal']
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlow hup

/-- The Wiener coordinate at real time `t`, recovered from the code. -/
def codeWiener (t : ℝ) (z : CodeSpace N) (q : (Fin N × Fin N) × Fin 2) : ℝ :=
  limUnder atTop (fun n : ℕ => z.2 q (n, ⌈2 ^ n * t⌉₊))

theorem codeWiener_flowCode (t : ℝ) (ω : FlowSample N) (q : (Fin N × Fin N) × Fin 2) :
    codeWiener t (flowCode ω) q = ω.2 q (Real.toNNReal t) :=
  (((ω.2 q).continuous.tendsto _).comp (tendsto_dyadicApprox t)).limUnder_eq

theorem measurable_codeWiener (q : (Fin N × Fin N) × Fin 2) :
    Measurable (fun p : ℝ × CodeSpace N => codeWiener p.1 p.2 q) := by
  refine (StronglyMeasurable.limUnder (f := fun (n : ℕ) (p : ℝ × CodeSpace N) =>
    p.2.2 q (n, ⌈2 ^ n * p.1⌉₊)) fun n => ?_).measurable
  have h : Measurable (fun x : ℕ × CodeSpace N => x.2.2 q (n, x.1)) :=
    measurable_from_prod_countable_right fun k =>
      (measurable_pi_apply (n, k)).comp ((measurable_pi_apply q).comp measurable_snd)
  exact (h.comp ((measurable_const.mul measurable_fst).nat_ceil.prodMk measurable_snd)).stronglyMeasurable

/-- The flow matrix rebuilt from the code. -/
def codeMatrix (F : Matrix (Fin N) (Fin N) ℂ) (a σ : ℝ) (z : CodeSpace N) :
    Matrix (Fin N) (Fin N) ℂ :=
  F + Matrix.of (fun i j => z.1 i j) + brownianOfCoords N (fun q => codeWiener (σ - a) z q)

theorem codeMatrix_flowCode (F : Matrix (Fin N) (Fin N) ℂ) (a σ : ℝ) (ω : FlowSample N) :
    codeMatrix F a σ (flowCode ω) = flowMatrix F a ω σ := by
  simp only [codeMatrix, flowMatrix, hermitianBrownian_eq_coords, codeWiener_flowCode]
  rfl

theorem measurable_codeMatrix (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) :
    Measurable (fun p : ℝ × CodeSpace N => codeMatrix F a p.1 p.2) := by
  have hW : Measurable (fun p : ℝ × CodeSpace N => fun q => codeWiener (p.1 - a) p.2 q) :=
    Measurable.of_eval fun q => (measurable_codeWiener q).comp
      ((measurable_fst.sub_const a).prodMk measurable_snd)
  have hB := measurable_brownianOfCoords.comp hW
  apply Measurable.of_eval_matrix
  intro i j
  simp only [codeMatrix, Matrix.add_apply, Matrix.of_apply]
  have h1 : Measurable (fun p : ℝ × CodeSpace N => p.2.1 i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  exact (measurable_const.add h1).add ((measurable_matrixEntry i j).comp hB)

/-!
## The clamped moments
-/

/-- `max(-M, min(M, x))`. -/
def clampAbs (M x : ℝ) : ℝ := max (-M) (min M x)

theorem clampAbs_of_abs_le {M x : ℝ} (h : |x| ≤ M) : clampAbs M x = x := by
  unfold clampAbs
  rw [min_eq_right (le_of_abs_le h), max_eq_right (neg_le_of_abs_le h)]

theorem abs_clampAbs_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |clampAbs M x| ≤ M := by
  unfold clampAbs
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem continuous_clampAbs (M : ℝ) : Continuous (clampAbs M) := by
  unfold clampAbs; fun_prop

/-- `K = max 1 (N ‖q‖²)`. -/
def overlapBound (N : ℕ) (q : Fin N → ℂ) : ℝ := max 1 ((N : ℝ) * ∑ i, ‖q i‖ ^ 2)

theorem one_le_overlapBound (q : Fin N → ℂ) : 1 ≤ overlapBound N q := le_max_left _ _

/-- Level `K^{|ζ|}` of the clamp. -/
def momentLevel (q : Fin N → ℂ) (ζ : Occ N) : ℝ := overlapBound N q ^ (∑ i, ζ i)

theorem momentLevel_nonneg (q : Fin N → ℂ) (ζ : Occ N) : 0 ≤ momentLevel q ζ :=
  pow_nonneg (le_trans zero_le_one (one_le_overlapBound q)) _

/-- Cauchy–Schwarz: `|q* v|² ≤ ‖q‖² ‖v‖²`. -/
theorem norm_dotProduct_sq_le (q v : Fin N → ℂ) :
    ‖star q ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖q i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  have h1 : ‖star q ⬝ᵥ v‖ ≤ ∑ i, ‖q i‖ * ‖v i‖ := by
    simp only [dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp
  have h3 : (∑ i, ‖q i‖ * ‖v i‖) ^ 2 ≤ (∑ i, ‖q i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h3

/-- On simple spectrum the overlaps lie in `[0, K]`. -/
theorem overlap_le {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hs : BlockBand.Internal.Contracts.Transmission.HasSimpleSpectrum N K) (q : Fin N → ℂ)
    (k : Fin N) : (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector K k‖ ^ 2 ≤ overlapBound N q := by
  have hunit : ∑ x, ‖freshEigenvector K k x‖ ^ 2 = 1 := by
    simp only [freshEigenvector, BlockBand.Model.Construction.rawOrderedColumnSelection_eq _ K hK]
    exact BlockBand.Model.Construction.sum_norm_sq_orderedColumnSelection _ ⟨K, hK⟩
      (injective_orderedEigenvalue hK hs)
  have := norm_dotProduct_sq_le q (freshEigenvector K k)
  rw [hunit, mul_one] at this
  exact (mul_le_mul_of_nonneg_left this (Nat.cast_nonneg N)).trans (le_max_right _ _)

theorem abs_momentMonomial_le {X : Fin N → ℝ} {B : ℝ} (hX0 : ∀ i, 0 ≤ X i)
    (hX : ∀ i, X i ≤ B) (ζ : Occ N) : |momentMonomial X ζ| ≤ B ^ (∑ i, ζ i) := by
  unfold momentMonomial
  rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => div_nonneg (pow_nonneg (hX0 i) _)
    (Nat.cast_nonneg _)), ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ => div_nonneg (pow_nonneg (hX0 i) _) (Nat.cast_nonneg _))
    fun i _ => ?_
  calc X i ^ ζ i / ((ζ i).factorial : ℝ) ≤ X i ^ ζ i :=
        div_le_self (pow_nonneg (hX0 i) _) (Nat.one_le_cast.2 (Nat.factorial_pos _))
    _ ≤ B ^ ζ i := pow_le_pow_left₀ (hX0 i) (hX i) _

/-- The moment observable of a matrix, clamped at `K^{|ζ|}`. -/
def clampedMomentOf (q : Fin N → ℂ) (ζ : Occ N) (K : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  clampAbs (momentLevel q ζ)
    (momentMonomial (fun k => (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector K k‖ ^ 2) ζ)

theorem measurable_clampedMomentOf (q : Fin N → ℂ) (ζ : Occ N) :
    Measurable (clampedMomentOf q ζ) :=
  (continuous_clampAbs _).measurable.comp ((measurable_momentMonomial ζ).comp
    (Measurable.of_eval fun k => measurable_overlapOf q k))

/-- `clamp(mono(X(σ)(ω), ζ))`. -/
def clampedMoment (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ) (ζ : Occ N) (σ : ℝ)
    (ω : FlowSample N) : ℝ :=
  clampedMomentOf q ζ (flowMatrix F a ω σ)

theorem clampedMoment_eq {F : Matrix (Fin N) (Fin N) ℂ} {a : ℝ} (q : Fin N → ℂ) (ζ : Occ N)
    {σ : ℝ} {ω : FlowSample N} (hH : (flowMatrix F a ω σ).IsHermitian)
    (hs : BlockBand.Internal.Contracts.Transmission.HasSimpleSpectrum N (flowMatrix F a ω σ)) :
    clampedMoment F a q ζ σ ω = momentMonomial (fun k => flowOverlap F a q σ k ω) ζ := by
  unfold clampedMoment clampedMomentOf
  apply clampAbs_of_abs_le
  exact abs_momentMonomial_le (fun k => by positivity)
    (fun k => overlap_le hH hs q k) ζ

theorem abs_clampedMoment_le (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ)
    (ζ : Occ N) (σ : ℝ) (ω : FlowSample N) : |clampedMoment F a q ζ σ ω| ≤ momentLevel q ζ :=
  abs_clampAbs_le (momentLevel_nonneg q ζ) _

theorem measurable_clampedMoment_uncurry (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ)
    (q : Fin N → ℂ) (ζ : Occ N) :
    Measurable (fun p : ℝ × FlowSample N => clampedMoment F a q ζ p.1 p.2) :=
  (measurable_clampedMomentOf q ζ).comp (measurable_flowMatrix_uncurry F a)

/-- The code form `g_ζ(σ, z)` of the clamped moment. -/
def codeMoment (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ) (ζ : Occ N)
    (p : ℝ × CodeSpace N) : ℝ :=
  clampedMomentOf q ζ (codeMatrix F a p.1 p.2)

theorem measurable_codeMoment (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ)
    (ζ : Occ N) : Measurable (codeMoment F a q ζ) :=
  (measurable_clampedMomentOf q ζ).comp (measurable_codeMatrix F a)

theorem codeMoment_flowCode (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ) (ζ : Occ N)
    (σ : ℝ) (ω : FlowSample N) : codeMoment F a q ζ (σ, flowCode ω) = clampedMoment F a q ζ σ ω := by
  simp [codeMoment, clampedMoment, codeMatrix_flowCode]

/-!
## The path map and the version
-/

/-- The eigenvalue path on `[s, c]`. -/
def pathMap (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (ω : FlowSample N) :
    Set.Icc s c → Fin N → ℝ :=
  fun σ k => flowEigenvalue F a ω σ k

theorem comap_pathMap (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) :
    MeasurableSpace.comap (pathMap F a s c) inferInstance = pathSigma F a s c := by
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    pathSigma, iSup_subtype']
  rfl

theorem measurable_pathMap (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) :
    Measurable (pathMap F a s c) :=
  Measurable.of_eval fun σ => Measurable.of_eval fun k => measurable_flowEigenvalue F a σ k

theorem measurable_pathMap_pathSigma (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) :
    Measurable[pathSigma F a s c] (pathMap F a s c) := by
  rw [← comap_pathMap]; exact comap_measurable _

/-- The regular conditional law of the code given the path. -/
def pathKernel (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) :
    Kernel (Set.Icc s c → Fin N → ℝ) (CodeSpace N) :=
  condDistrib flowCode (pathMap F a s c) (flowLaw N a)

instance (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) : IsMarkovKernel (pathKernel F a s c) := by
  unfold pathKernel; infer_instance

/-- The version on path space: `(σ, x) ↦ ∫ g_ζ(σ, z) dκ_x(z)`. -/
def versionOnPath (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ) (ζ : Occ N)
    (p : ℝ × (Set.Icc s c → Fin N → ℝ)) : ℝ :=
  ∫ z, codeMoment F a q ζ (p.1, z) ∂pathKernel F a s c p.2

theorem measurable_versionOnPath (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ)
    (ζ : Occ N) : Measurable (versionOnPath F a s c q ζ) := by
  have h := StronglyMeasurable.integral_kernel_prod_right'
    (κ := Kernel.prodMkLeft ℝ (pathKernel F a s c))
    (f := fun x : (ℝ × (Set.Icc s c → Fin N → ℝ)) × CodeSpace N => codeMoment F a q ζ (x.1.1, x.2))
    ((measurable_codeMoment F a q ζ).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  have e : versionOnPath F a s c q ζ =
      fun x => ∫ y, codeMoment F a q ζ (x.1, y) ∂(pathKernel F a s c) x.2 := rfl
  rw [e]
  simpa [Kernel.prodMkLeft_apply] using h.measurable

/-- **The jointly measurable version** `Φ̃_ζ(σ, ω)`. -/
def momentVersion (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ) (ζ : Occ N)
    (σ : ℝ) (ω : FlowSample N) : ℝ :=
  versionOnPath F a s c q ζ (σ, pathMap F a s c ω)

/-- Joint measurability for `borel ⊗ 𝓛`. -/
theorem measurable_momentVersion_pathSigma (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ)
    (q : Fin N → ℂ) (ζ : Occ N) :
    Measurable[@Prod.instMeasurableSpace ℝ (FlowSample N) _ (pathSigma F a s c)]
      (fun p : ℝ × FlowSample N => momentVersion F a s c q ζ p.1 p.2) :=
  (measurable_versionOnPath F a s c q ζ).comp
    (measurable_fst.prodMk ((measurable_pathMap_pathSigma F a s c).comp measurable_snd))

theorem measurable_momentVersion (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ)
    (ζ : Occ N) : Measurable (fun p : ℝ × FlowSample N => momentVersion F a s c q ζ p.1 p.2) :=
  (measurable_versionOnPath F a s c q ζ).comp
    (measurable_fst.prodMk ((measurable_pathMap F a s c).comp measurable_snd))

/-- Each time slice is `𝓛`-measurable. -/
theorem measurable_momentVersion_slice (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ)
    (q : Fin N → ℂ) (ζ : Occ N) (σ : ℝ) :
    Measurable[pathSigma F a s c] (momentVersion F a s c q ζ σ) :=
  (measurable_versionOnPath F a s c q ζ).comp
    (measurable_const.prodMk (measurable_pathMap_pathSigma F a s c))

theorem abs_momentVersion_le (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ)
    (ζ : Occ N) (σ : ℝ) (ω : FlowSample N) : |momentVersion F a s c q ζ σ ω| ≤ momentLevel q ζ := by
  unfold momentVersion versionOnPath
  have h := norm_integral_le_of_norm_le_const (μ := pathKernel F a s c (pathMap F a s c ω))
    (f := fun z => codeMoment F a q ζ (σ, z)) (C := momentLevel q ζ)
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact abs_clampAbs_le (momentLevel_nonneg q ζ) _)
  simpa [Real.norm_eq_abs] using h

/-- **Version property**: `Φ̃_ζ(σ) = E[clamp(mono(X(σ), ζ)) | 𝓛]` almost surely, for each `σ`. -/
theorem momentVersion_ae_eq (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ)
    (ζ : Occ N) (σ : ℝ) :
    momentVersion F a s c q ζ σ =ᵐ[flowLaw N a]
      (flowLaw N a)[clampedMoment F a q ζ σ | pathSigma F a s c] := by
  have hint : Integrable (fun ω => codeMoment F a q ζ (σ, flowCode ω)) (flowLaw N a) := by
    refine Integrable.of_bound (C := momentLevel q ζ)
      ((measurable_codeMoment F a q ζ).comp
        (measurable_const.prodMk measurable_flowCode)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_clampAbs_le (momentLevel_nonneg q ζ) _
  have hm : Measurable (fun z : CodeSpace N => codeMoment F a q ζ (σ, z)) :=
    (measurable_codeMoment F a q ζ).comp (measurable_const.prodMk measurable_id)
  have h := condExp_ae_eq_integral_condDistrib (μ := flowLaw N a) (measurable_pathMap F a s c)
    measurable_flowCode.aemeasurable (f := fun z : CodeSpace N => codeMoment F a q ζ (σ, z))
    hm.stronglyMeasurable hint
  rw [comap_pathMap] at h
  have he : (fun ω => codeMoment F a q ζ (σ, flowCode ω)) = clampedMoment F a q ζ σ := by
    funext ω; exact codeMoment_flowCode F a q ζ σ ω
  rw [he] at h
  exact h.symm

end BlockBand.Palm.MomentFlow
