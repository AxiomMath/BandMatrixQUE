module

public import BlockBand.Critical.MatrixClosing.Poles.Laplace
public import BlockBand.Critical.MatrixClosing.Poles.AtomSum
public import BlockBand.Critical.Herglotz.Near
public import BlockBand.Critical.DecoratedSine.Existence
public import BlockBand.Endpoints.VagueMeasurability

/-!
# Hypothesis 1 for the collar: reduction to Laplace functionals

* `canonTest φ : C_c(ℝ × ℂ^r, ℝ)`, `(x, g) ↦ φ(x, π⁻¹gg^*)` (`canonicalResidue` is proper).
* `CollarPolesAt r`: `CollarPolesClause` at a fixed frame rank (`collarPolesClause_iff_forall`).
* **`CollarPolesLaplaceAt r`** (`CollarPolesLaplaceClause = ∀ r, CollarPolesLaplaceAt r`):
  along every admissible old sequence, for every nonnegative `φ ∈ C_c(ℝ × Matrix, ℝ)`,
  `E_collar exp(-Σ_{poles x} φ(x, μ_W({x}))) → decoratedSineLaplace r (canonTest φ)` (the
  decorated sine Laplace functional at `(x, g) ↦ φ(x, π⁻¹gg^*)`). This is the Laplace-functional
  form in which the relative mixed vectors theorem (conditionally on `A, B`, then averaging)
  produces hypothesis 1.
* **`collarPolesAt_of_laplaceAt : CollarPolesLaplaceAt r → CollarPolesAt r`** and
  `collarPolesClause_of_laplace`: `f_k = f_k⁺ - f_k⁻`, the multivariate Laplace continuity
  theorem for the `2m` nonnegative coordinates, the decorated-sine Laplace identity
  (`IsDecoratedSineProcess.laplace`) on the limit side, and the continuous mapping theorem.
* **`laplaceAt_of_collarPolesAt`**, `collarPolesAt_iff_laplaceAt`, `collarPolesClause_iff_laplace`:
  the converse, through one decorated sine process (`DecoratedSine.exists_isDecoratedSineProcess`).
  So the Laplace form is exactly equivalent to hypothesis 1, rank by rank: the reduction neither
  weakens nor strengthens it. (At `r = 0` both are false.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Herglotz
open scoped NNReal

variable {r : ℕ}

/-!
## The canonical test `(x, g) ↦ φ(x, π⁻¹gg^*)`
-/

theorem isCompact_preimage_canonMap {K : Set (ℝ × Matrix (Fin r) (Fin r) ℂ)} (hK : IsCompact K) :
    IsCompact ((fun p : ℝ × (Fin r → ℂ) => (p.1, canonicalResidue p.2)) ⁻¹' K) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ q ∈ K, matNorm q.2 ≤ B := by
    obtain ⟨B, hB⟩ := (hK.image (continuous_matNorm.comp continuous_snd)).bddAbove
    exact ⟨B, fun q hq => hB ⟨q, hq, rfl⟩⟩
  set T : Set (ℝ × (Fin r → ℂ)) := (Prod.fst '' K) ×ˢ
    (Set.pi Set.univ fun _ : Fin r => Metric.closedBall (0 : ℂ) (Real.sqrt (Real.pi * B)))
  have hT : IsCompact T :=
    (hK.image continuous_fst).prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  refine hT.of_isClosed_subset (hK.isClosed.preimage continuous_canonMap) ?_
  intro p hp
  refine ⟨⟨_, hp, rfl⟩, ?_⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i
  have h1 := norm_sq_le_matNorm_canonicalResidue p.2 i
  have h2 := hB _ hp
  refine Real.le_sqrt_of_sq_le ?_
  have := Real.pi_pos
  nlinarith

/-- `(x, g) ↦ φ(x, π⁻¹gg^*)` as a compactly supported continuous test on `ℝ × ℂ^r`. -/
def canonTest (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ :=
  ⟨⟨fun p => φ (p.1, canonicalResidue p.2), φ.continuous.comp continuous_canonMap⟩,
    (isCompact_preimage_canonMap φ.hasCompactSupport).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset_preimage φ continuous_canonMap)⟩

theorem canonTest_apply (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ)
    (p : ℝ × (Fin r → ℂ)) : canonTest φ p = φ (p.1, canonicalResidue p.2) := rfl

/-- `φ ↦ ∫ φ(x, π⁻¹gg^*) dξ` as an `ℝ`-linear map. -/
def canonCoordLinear (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) :
    CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ →ₗ[ℝ] ℝ where
  toFun φ := ∫ p, φ (p.1, canonicalResidue p.2) ∂ξ.measure
  map_add' φ ψ := by
    have hφ : Integrable (canonTest φ) ξ.measure :=
      (canonTest φ).continuous.integrable_of_hasCompactSupport (canonTest φ).hasCompactSupport
    have hψ : Integrable (canonTest ψ) ξ.measure :=
      (canonTest ψ).continuous.integrable_of_hasCompactSupport (canonTest ψ).hasCompactSupport
    simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
    exact integral_add hφ hψ
  map_smul' c φ := by
    simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    exact integral_const_mul c _

theorem canonCoordLinear_apply (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ)))
    (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    canonCoordLinear ξ φ = ∫ p, φ (p.1, canonicalResidue p.2) ∂ξ.measure := rfl

/-!
## The Laplace-functional form of hypothesis 1
-/

/-- **Hypothesis 1 for the collar at a fixed frame rank `r`**: the body of
`CollarPolesClause` with `r` fixed (`collarPolesClause_iff_forall`). -/
def CollarPolesAt (r : ℕ) : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (S : OldSequence b κ r)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))), IsDecoratedSineProcess r P' Ξ →
    ∀ (m : ℕ) (f : Fin m → CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ),
      TendstoInDistribution (fun N ω k => (S.collarFns N ω).atomSum (f k)) atTop
        (fun ω k => ∫ p, f k (p.1, canonicalResidue p.2) ∂(Ξ ω).measure)
        (fun N => collarLaw (S.W N) b) P'

theorem collarPolesClause_iff_forall : CollarPolesClause ↔ ∀ r, CollarPolesAt r :=
  ⟨fun h r b hb0 hb κ hκ S => h b hb0 hb κ hκ r S,
    fun h b hb0 hb κ hκ r S => h r b hb0 hb κ hκ S⟩

/-- **Hypothesis 1 for the collar, Laplace form, at a fixed frame rank `r`**: along every
admissible old sequence, for every nonnegative `φ ∈ C_c(ℝ × Matrix, ℝ)`, the Laplace functional of
the marked poles and residues of `F_{W_n}` under `collarLaw` converges to the decorated sine
Laplace functional (`decoratedSineLaplace`) of `(x, g) ↦ φ(x, π⁻¹gg^*)`. Equivalent to
`CollarPolesAt r` (`collarPolesAt_iff_laplaceAt`). For `r ≥ 1` it follows from the relative mixed
vectors theorem (decorated clause, conditionally on `A, B`), the regularity certificate, the
intensity and the collar projection covariance after averaging over `A, B`
(`collarPolesAt_of_relativeVectors`, with `RelativeMixedVectorsStatement` as a hypothesis). It is
false for `r = 0`.
-/
def CollarPolesLaplaceAt (r : ℕ) : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (S : OldSequence b κ r)
    (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ), (∀ p, 0 ≤ φ p) →
      Tendsto (fun N => ∫ ω, Real.exp (-(S.collarFns N ω).atomSum φ) ∂collarLaw (S.W N) b) atTop
        (𝓝 (decoratedSineLaplace r (canonTest φ)))

/-- The Laplace form at every rank (equivalent to `CollarPolesClause`). -/
def CollarPolesLaplaceClause : Prop := ∀ r, CollarPolesLaplaceAt r

/-- Positive (`true`) and negative (`false`) parts of a family of tests. -/
def signedParts {m : ℕ}
    (f : Fin m → CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ)
    (j : Fin m × Bool) : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ :=
  if j.2 then (f j.1).nnrealPart.toReal else (-(f j.1)).nnrealPart.toReal

theorem signedParts_nonneg {m : ℕ}
    (f : Fin m → CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ)
    (j : Fin m × Bool) (p : ℝ × Matrix (Fin r) (Fin r) ℂ) : 0 ≤ signedParts f j p := by
  unfold signedParts
  split_ifs <;> simp

theorem signedParts_sub {m : ℕ}
    (f : Fin m → CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) (k : Fin m) :
    signedParts f (k, true) - signedParts f (k, false) = f k := by
  simp only [signedParts, ite_true]
  exact CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg (f k)

/-- **The Laplace form implies hypothesis 1**, rank by rank. -/
theorem collarPolesAt_of_laplaceAt {r : ℕ} (h : CollarPolesLaplaceAt r) : CollarPolesAt r := by
  intro b hb0 hb κ hκ S Ω' _ P' _ Ξ hΞ m f
  set g := signedParts f
  set Z : ∀ N, CollarSample (S.W N) → Fin m × Bool → ℝ :=
    fun N ω j => atomSumLinear (S.collarFns N ω) (g j)
  set Z' : Ω' → Fin m × Bool → ℝ := fun ω j => canonCoordLinear (Ξ ω) (g j)
  have hconv : TendstoInDistribution Z atTop Z' (fun N => collarLaw (S.W N) b) P' := by
    refine tendstoInDistribution_of_laplace (fun N => ?_) ?_ (fun N ω j => ?_) (fun ω j => ?_)
      (fun t => ?_)
    · exact (Measurable.of_eval fun j =>
        measurable_atomSum_collarFunction b (S.e N) (S.X N) (S.J N) (g j)).aemeasurable
    · exact (Measurable.of_eval fun j =>
        (BlockBand.Endpoints.measurable_coordinate (canonTest (g j))).comp
          hΞ.measurable).aemeasurable
    · exact atomSum_nonneg _ (signedParts_nonneg f j)
    · exact integral_nonneg fun p => signedParts_nonneg f j _
    · set φ := ∑ j, (t j : ℝ) • g j
      have hφ0 : ∀ p, 0 ≤ φ p := by
        intro p
        simp only [φ, CompactlySupportedContinuousMap.coe_sum, Finset.sum_apply,
          CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (t j).2 (signedParts_nonneg f j p)
      have e1 : ∀ N ω, ∑ j, (t j : ℝ) * Z N ω j = (S.collarFns N ω).atomSum φ := by
        intro N ω
        rw [← atomSumLinear_apply, map_sum]
        simp only [map_smul, smul_eq_mul, Z]
      have e2 : ∀ ω, ∑ j, (t j : ℝ) * Z' ω j = ∫ z, canonTest φ z ∂(Ξ ω).measure := by
        intro ω
        rw [show (∫ z, canonTest φ z ∂(Ξ ω).measure) = canonCoordLinear (Ξ ω) φ from rfl,
          map_sum]
        simp only [map_smul, smul_eq_mul, Z']
      simp only [e1, e2]
      rw [hΞ.laplace (canonTest φ) (fun z => hφ0 _)]
      exact h b hb0 hb κ hκ S φ hφ0
  have hD : Continuous fun y : Fin m × Bool → ℝ => fun k : Fin m => y (k, true) - y (k, false) :=
    continuous_pi fun k => (continuous_apply _).sub (continuous_apply _)
  have h2 := hconv.continuous_comp hD
  have e1 : (fun N => (fun y : Fin m × Bool → ℝ => fun k : Fin m => y (k, true) - y (k, false)) ∘
      Z N) = fun N ω k => (S.collarFns N ω).atomSum (f k) := by
    funext N ω k
    simp only [Function.comp_apply, Z, ← map_sub, g, signedParts_sub]
    rfl
  have e2 : (fun y : Fin m × Bool → ℝ => fun k : Fin m => y (k, true) - y (k, false)) ∘ Z' =
      fun ω k => ∫ p, f k (p.1, canonicalResidue p.2) ∂(Ξ ω).measure := by
    funext ω k
    simp only [Function.comp_apply, Z', ← map_sub, g, signedParts_sub]
    rfl
  rw [e1, e2] at h2
  exact h2

/-- **The converse**: hypothesis 1 gives its Laplace form (one decorated sine process, test
`y ↦ exp(-ψ(y))` with `ψ = id` on `[0, ∞)`). -/
theorem laplaceAt_of_collarPolesAt {r : ℕ} (h : CollarPolesAt r) : CollarPolesLaplaceAt r := by
  intro b hb0 hb κ hκ S φ hφ
  obtain ⟨Ω', _, P', Ξ, hΞ⟩ := BlockBand.Critical.DecoratedSine.exists_isDecoratedSineProcess r
  have := hΞ.prob
  have hT := h b hb0 hb κ hκ S Ω' P' Ξ hΞ 1 (fun _ => φ)
  have hI := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hT.forall_aemeasurable
    hT.aemeasurable_limit).1 hT (lapTest fun _ => (1 : ℝ≥0))
  have e1 : ∀ N ω, lapTest (fun _ => (1 : ℝ≥0))
      (fun _ : Fin 1 => (S.collarFns N ω).atomSum φ) =
        Real.exp (-(S.collarFns N ω).atomSum φ) := by
    intro N ω
    rw [lapTest_apply_of_nonneg _ (fun _ => atomSum_nonneg _ hφ)]
    simp
  have e2 : ∀ ω, lapTest (fun _ => (1 : ℝ≥0))
      (fun _ : Fin 1 => ∫ p, φ (p.1, canonicalResidue p.2) ∂(Ξ ω).measure) =
        Real.exp (-∫ z, canonTest φ z ∂(Ξ ω).measure) := by
    intro ω
    rw [lapTest_apply_of_nonneg _ (fun _ => integral_nonneg fun p => hφ _)]
    simp [canonTest_apply]
  simp only [e1, e2] at hI
  rw [hΞ.laplace (canonTest φ) (fun z => hφ _)] at hI
  exact hI

theorem collarPolesAt_iff_laplaceAt (r : ℕ) : CollarPolesAt r ↔ CollarPolesLaplaceAt r :=
  ⟨laplaceAt_of_collarPolesAt, collarPolesAt_of_laplaceAt⟩

/-- **The Laplace form implies hypothesis 1**, all ranks. -/
theorem collarPolesClause_of_laplace (h : CollarPolesLaplaceClause) : CollarPolesClause :=
  collarPolesClause_iff_forall.2 fun r => collarPolesAt_of_laplaceAt (h r)

/-- **Hypothesis 1 is equivalent to its Laplace form.** -/
theorem collarPolesClause_iff_laplace : CollarPolesClause ↔ CollarPolesLaplaceClause :=
  ⟨fun h r => laplaceAt_of_collarPolesAt (collarPolesClause_iff_forall.1 h r),
    collarPolesClause_of_laplace⟩

end BlockBand.Critical.MatrixClosing.Poles
