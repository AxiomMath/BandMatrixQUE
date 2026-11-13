module

public import BlockBand.Critical.EntireLaw.Measurability
public import BlockBand.Critical.GlobalSource.Bridge
public import BlockBand.Critical.MatrixClosing.Bridge

/-!
# The entire law: scaling of the global probe law and reality of `𝒯_jj`

* (a) `globalProbeMatrix_smul`: `𝒦_W(tQ) = t 𝒦_W(Q)`, `t ≥ 0` (every sample);
  `isGlobalProbeCriticalLimit_smul`: if `κ` is the critical limit of `(𝒦_W(Q), B_W(Q))`, then
  `(t•)_# κ` is that of `(𝒦_W(tQ), B_W(tQ))`; `isGlobalProbeCriticalLimit_unique` (`τ ≥ 0`,
  probability measures); hence `globalProbeLaw_smul_eq_map`: `κ_{tQ} = (t•)_# κ_Q`.
  `cfc_sqrt_smul` (`cfc √ (tB) = √t cfc √ B`, `B` Hermitian) and `closedSourceMatrix_smul`:
  `𝒯(tK, C) = t 𝒯(K, C)`.
* (b) `ae_closedSourceMatrix_isHermitian`, `ae_closedSourceMatrix_diag_im`: for a realization
  of `𝖢_J(0)`, a.s. `𝒯(K, 𝖢_J(0))` is Hermitian for every `K`, so `Im 𝒯_jj = 0`
  (`MatrixClosing.ae_isHermitian_of_isCanonicalCauchyAtZero`, `closedSourceMatrix_isHermitian`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.GlobalSource
open scoped ComplexConjugate

variable {J : ℕ}

/-- `√(t q) = √t √q` inside the global probe vector. -/
theorem globalProbeVector_smul (W n : ℕ) (Q : C(Torus, ℝ)) {t : ℝ} (ht : 0 ≤ t)
    (g : PathSite W n → ℂ) :
    globalProbeVector W n (t • Q) g = ((Real.sqrt t : ℝ) : ℂ) • globalProbeVector W n Q g := by
  funext x
  simp only [globalProbeVector, pathProfileValue, ContinuousMap.smul_apply, smul_eq_mul,
    Pi.smul_apply, Real.sqrt_mul ht]
  push_cast
  ring

/-- **`𝒦_W(tQ) = t 𝒦_W(Q)`** for `t ≥ 0`. -/
theorem globalProbeMatrix_smul (b E : ℝ) (W n : ℕ) (Q : Fin J → C(Torus, ℝ)) {t : ℝ}
    (ht : 0 ≤ t) (x : GlobalProbeSample W n J) :
    globalProbeMatrix b E W n (fun a => t • Q a) x = t • globalProbeMatrix b E W n Q x := by
  ext a c
  simp only [globalProbeMatrix, globalProbeVector_smul W n _ ht, Matrix.smul_apply]
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt ht, Complex.real_smul]

/-- `Im (tK) = t Im K` for real `t`. -/
theorem imPart_smul {ι : Type*} [Fintype ι] (t : ℝ) (K : Matrix ι ι ℂ) :
    BlockBand.Internal.Contracts.Critical.imPart (t • K) =
      t • BlockBand.Internal.Contracts.Critical.imPart K := by
  unfold BlockBand.Internal.Contracts.Critical.imPart
  rw [conjTranspose_smul, star_trivial, ← smul_sub, smul_comm]

/-- `B(tK) = t B(K)`. -/
theorem probeGram_smul (b E : ℝ) {ι : Type*} [Fintype ι] (t : ℝ) (K : Matrix ι ι ℂ) :
    probeGram b E (t • K) = t • probeGram b E K := by
  unfold probeGram
  rw [imPart_smul, smul_comm]

/-- `Re (tK) = t Re K`. -/
theorem matrixRePart_smul {ι : Type*} [Fintype ι] (t : ℝ) (K : Matrix ι ι ℂ) :
    matrixRePart (t • K) = t • matrixRePart K := by
  unfold matrixRePart
  rw [conjTranspose_smul, star_trivial, ← smul_add, smul_comm]

/-- `cfc √ (tB) = √t cfc √ B` for `t ≥ 0` and Hermitian `B`. -/
theorem cfc_sqrt_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℝ} (ht : 0 ≤ t)
    {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    cfc Real.sqrt (t • B) = Real.sqrt t • cfc Real.sqrt B := by
  have hB' : IsSelfAdjoint B := hB
  rw [← cfc_comp_smul t Real.sqrt B (ha := hB')]
  have : (fun x : ℝ => Real.sqrt (t • x)) = fun x => Real.sqrt t * Real.sqrt x := by
    funext x; rw [smul_eq_mul, Real.sqrt_mul ht]
  rw [show (Real.sqrt <| t • ·) = fun x : ℝ => Real.sqrt (t • x) from rfl, this]
  exact cfc_const_mul _ _ _

/-- **`𝒯(tK, C) = t 𝒯(K, C)`** for `t ≥ 0`. -/
theorem closedSourceMatrix_smul (b E : ℝ) {t : ℝ} (ht : 0 ≤ t) (K C : Matrix (Fin J) (Fin J) ℂ) :
    closedSourceMatrix b E (t • K) C = t • closedSourceMatrix b E K C := by
  unfold closedSourceMatrix
  rw [matrixRePart_smul, probeGram_smul, cfc_sqrt_smul ht (probeGram_isHermitian b E K),
    smul_add]
  congr 1
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul, Real.mul_self_sqrt ht,
    smul_comm]

attribute [local instance] matrix_hasOuterApproxClosed

/-- **Scaling of the critical limit**: if `κ` is the critical limit of `(𝒦_W(Q), B_W(Q))`, then
`(t•)_# κ` is that of `(𝒦_W(tQ), B_W(tQ))`, `t ≥ 0`. -/
theorem isGlobalProbeCriticalLimit_smul {b E τ : ℝ} {Q : Fin J → C(Torus, ℝ)}
    {κ : Measure (Matrix (Fin J) (Fin J) ℂ)} (hκ : IsGlobalProbeCriticalLimit b E τ Q κ)
    {t : ℝ} (ht : 0 ≤ t) :
    IsGlobalProbeCriticalLimit b E τ (fun a => t • Q a)
      (κ.map fun K => t • K) := by
  intro s Φ
  let g : C(Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ,
      Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ) :=
    ⟨fun p => (t • p.1, t • p.2), (continuous_fst.const_smul t).prodMk
      (continuous_snd.const_smul t)⟩
  have h := hκ s (Φ.compContinuous g)
  have hm : Measurable fun K : Matrix (Fin J) (Fin J) ℂ => t • K := measurable_const_smul t
  have hcont : Continuous fun K : Matrix (Fin J) (Fin J) ℂ => Φ (K, probeGram b E K) :=
    Φ.continuous.comp (continuous_id.prodMk (continuous_probeGram b E))
  rw [integral_map hm.aemeasurable hcont.aestronglyMeasurable]
  have e2 : ∫ K, (Φ.compContinuous g) (K, probeGram b E K) ∂κ =
      ∫ K, Φ (t • K, probeGram b E (t • K)) ∂κ := by
    refine integral_congr_ae (Eventually.of_forall fun K => ?_)
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, g,
      probeGram_smul]
  rw [e2] at h
  refine h.congr fun j => ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, g,
    globalProbeGram, globalProbeMatrix_smul b E _ _ Q ht, probeGram_smul]

/-- **Uniqueness of the critical limit** (`τ ≥ 0`, so critical sequences exist): two probability
measures that are critical limits of the same `(𝒦_W, B_W)` coincide. -/
theorem isGlobalProbeCriticalLimit_unique {b E τ : ℝ} (hτ : 0 ≤ τ) {Q : Fin J → C(Torus, ℝ)}
    {κ κ' : Measure (Matrix (Fin J) (Fin J) ℂ)} [IsProbabilityMeasure κ]
    [IsProbabilityMeasure κ'] (h : IsGlobalProbeCriticalLimit b E τ Q κ)
    (h' : IsGlobalProbeCriticalLimit b E τ Q κ') : κ = κ' := by
  obtain ⟨s⟩ := exists_criticalSequence hτ
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun φ => ?_
  let g : C(Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ, Matrix (Fin J) (Fin J) ℂ) :=
    ⟨Prod.fst, continuous_fst⟩
  exact tendsto_nhds_unique (h s (φ.compContinuous g)) (h' s (φ.compContinuous g))

/-- **`κ_{tQ} = (t•)_# κ_Q`**: for `t ≥ 0`, the global probe law of the profiles
`tQ` (any law that is a probability measure and the critical limit of `(𝒦_W(tQ), B_W(tQ))`, in
particular the law of the global Gaussian source statement) is the image of that of `Q` under
`K ↦ tK`. -/
theorem globalProbeLaw_smul_eq_map {b E τ : ℝ} (hτ : 0 ≤ τ) {Q : Fin J → C(Torus, ℝ)}
    {κ κt : Measure (Matrix (Fin J) (Fin J) ℂ)} [IsProbabilityMeasure κ]
    [IsProbabilityMeasure κt] (hκ : IsGlobalProbeCriticalLimit b E τ Q κ) {t : ℝ} (ht : 0 ≤ t)
    (hκt : IsGlobalProbeCriticalLimit b E τ (fun a => t • Q a) κt) :
    κt = κ.map fun K => t • K := by
  exact isGlobalProbeCriticalLimit_unique hτ hκt (isGlobalProbeCriticalLimit_smul hκ ht)

/-- **Reality of `𝒯`**: a realization of `𝖢_J(0)` makes `𝒯(K, 𝖢_J(0))` Hermitian for every `K`,
almost surely; in particular its diagonal entries (`Im 𝒯_jj = 0`) are real a.s. -/
theorem ae_closedSourceMatrix_isHermitian (b E : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin J → ℂ))}
    {C : Ω → Matrix (Fin J) (Fin J) ℂ} (hC : IsCanonicalCauchyAtZero J P Ξ C) :
    ∀ᵐ ω ∂P, ∀ K : Matrix (Fin J) (Fin J) ℂ, (closedSourceMatrix b E K (C ω)).IsHermitian := by
  filter_upwards [BlockBand.Critical.MatrixClosing.ae_isHermitian_of_isCanonicalCauchyAtZero hC]
    with ω hω K
  exact BlockBand.Critical.MatrixClosing.closedSourceMatrix_isHermitian b E K hω

/-- `Im 𝒯_jj = 0` a.s., for every `K`. -/
theorem ae_closedSourceMatrix_diag_im (b E : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin J → ℂ))}
    {C : Ω → Matrix (Fin J) (Fin J) ℂ} (hC : IsCanonicalCauchyAtZero J P Ξ C) :
    ∀ᵐ ω ∂P, ∀ (K : Matrix (Fin J) (Fin J) ℂ) (j : Fin J),
      (closedSourceMatrix b E K (C ω) j j).im = 0 := by
  filter_upwards [ae_closedSourceMatrix_isHermitian b E hC] with ω hω K j
  have := congrFun (congrFun (hω K) j) j
  rw [conjTranspose_apply, Complex.star_def] at this
  exact Complex.conj_eq_iff_im.1 this

end BlockBand.Critical.EntireLaw
