module

public import BlockBand.DeterminantScore.SpectralConvexity

/-!
# The variance clause of indexed spectral convexity

`BrascampLiebStatement` is the Brascamp–Lieb inequality on an open convex set, with a diagonal
lower bound of the Hessian (proof: Neumann problem on a convex exhaustion, Bochner
identity, Cauchy–Schwarz in the Hessian metric, smooth convex approximation and weighted Sobolev
approximation): if `e^{-𝒰}` is a probability density on an open convex `D`, `𝒰 ∈ C²(D)` and
`∇²𝒰 ⪰ diag(w)` on `D` with `w > 0`, then every measurable `f`, smooth on `D`, of finite
weighted energy satisfies `Var f ≤ E Σ_j |∂_j f|²/w_j`. It is stated as a named `Prop` and used as
a hypothesis (Prékopa's theorem only gives log-concavity of marginals).

## Main results

* `variance_of_density`: the `density` clause of `IndexedSpectralConvexityStatement` together
  with `BrascampLiebStatement` implies its `variance` clause (the push-forward of the
  normalized sector law under the increasing eigenvalues is `e^{-𝒰} dλ` on the chamber, the
  chamber is convex, and dropping the Vandermonde terms of the spectral curvature gives the
  diagonal weight `t⁻¹ + 2λ_j⁻²`);
* `indexedSpectralConvexity_of`: `OrderedEigenDensityStatement` and `BrascampLiebStatement`
  imply `IndexedSpectralConvexityStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SpectralConvexity

open MeasureTheory ProbabilityTheory Matrix BlockBand.DeterminantScore
open BlockBand.DeterminantScore.Sector BlockBand.DeterminantScore.NegativeSpread
open scoped ENNReal NNReal ContDiff

variable {m : ℕ}

/-- The probability law `e^{-𝒰(λ)} dλ` on `D`. -/
def gibbsOn (D : Set (Fin m → ℝ)) (𝒰 : (Fin m → ℝ) → ℝ) : Measure (Fin m → ℝ) :=
  (volume.restrict D).withDensity fun lam => ENNReal.ofReal (Real.exp (-𝒰 lam))

/-- **Brascamp–Lieb inequality on an open convex set with a diagonal Hessian bound**, as used
in the proof of indexed spectral convexity. It is a hypothesis of `variance_of_density`. -/
def BrascampLiebStatement : Prop :=
  ∀ (m : ℕ) (D : Set (Fin m → ℝ)), IsOpen D → Convex ℝ D →
    ∀ (𝒰 : (Fin m → ℝ) → ℝ) (w : (Fin m → ℝ) → Fin m → ℝ), ContDiffOn ℝ 2 𝒰 D →
    (∀ lam ∈ D, ∀ j, 0 < w lam j) →
    (∀ lam ∈ D, ∀ a : Fin m → ℝ,
      ∑ j, w lam j * a j ^ 2 ≤ iteratedFDeriv ℝ 2 𝒰 lam (fun _ => a)) →
    IsProbabilityMeasure (gibbsOn D 𝒰) →
    ∀ f : (Fin m → ℝ) → ℝ, Measurable f → ContDiffOn ℝ ∞ f D →
      (∫⁻ lam, ENNReal.ofReal (∑ j, (fderiv ℝ f lam (Pi.single j 1)) ^ 2 / w lam j)
        ∂gibbsOn D 𝒰) ≠ ⊤ →
      evariance f (gibbsOn D 𝒰) ≤
        ∫⁻ lam, ENNReal.ofReal (∑ j, (fderiv ℝ f lam (Pi.single j 1)) ^ 2 / w lam j)
          ∂gibbsOn D 𝒰

/-- The fixed-inertia chamber is convex. -/
theorem convex_chamber (ℓ : ℕ) : Convex ℝ (chamber m ℓ) := by
  intro x hx y hy a b ha hb hab
  have key : ∀ u v u' v' : ℝ, u < v → u' < v' → a * u + b * u' < a * v + b * v' := by
    intro u v u' v' huv hu'v'
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' (sub_pos.2 huv), mul_nonneg hb (sub_pos.2 hu'v').le]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      linarith
  refine ⟨fun i j hij => ?_, fun k => ⟨fun hk => ?_, fun hk => ?_⟩⟩
  · simpa using key _ _ _ _ (hx.1 hij) (hy.1 hij)
  · simpa using key _ _ _ _ ((hx.2 k).1 hk) ((hy.2 k).1 hk)
  · simpa using key _ _ _ _ ((hx.2 k).2 hk) ((hy.2 k).2 hk)

/-- Variance is transported by push-forward. -/
theorem evariance_comp_eq_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {φ : α → β} (hφ : Measurable φ) {f : β → ℝ} (hf : Measurable f) :
    evariance (fun x => f (φ x)) μ = evariance f (μ.map φ) := by
  rw [evariance, evariance, integral_map hφ.aemeasurable hf.aestronglyMeasurable,
    lintegral_map ((hf.sub_const _).enorm.pow_const 2) hφ]

/-- The `variance` clause from the `density` clause and the Brascamp–Lieb inequality. -/
theorem variance_of_density
    (hdens : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
      K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
      ∃ 𝒰 : (Fin m → ℝ) → ℝ, ContDiffOn ℝ 2 𝒰 (chamber m ℓ) ∧
        (∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
          (∫⁻ x, ENNReal.ofReal (sectorDetSq K ℓ x).re * g (orderedEigs K x)
            ∂hermGaussian m t) =
            ENNReal.ofReal (sectorMass m t K ℓ).re *
              ∫⁻ lam in chamber m ℓ, ENNReal.ofReal (Real.exp (-𝒰 lam)) * g lam) ∧
        ∀ lam ∈ chamber m ℓ, ∀ a : Fin m → ℝ,
          curvatureForm (t : ℝ) lam a ≤ iteratedFDeriv ℝ 2 𝒰 lam (fun _ => a))
    (hBL : BrascampLiebStatement) :
    ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
      K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
      ∀ f : (Fin m → ℝ) → ℝ, Measurable f → ContDiffOn ℝ ∞ f (chamber m ℓ) →
        (∫⁻ x, ENNReal.ofReal (weightedEnergy (t : ℝ) f (orderedEigs K x))
          ∂sectorLaw m t K ℓ) ≠ ⊤ →
        evariance (fun x => f (orderedEigs K x)) (sectorLaw m t K ℓ) ≤
          ∫⁻ x, ENNReal.ofReal (weightedEnergy (t : ℝ) f (orderedEigs K x))
            ∂sectorLaw m t K ℓ := by
  intro m t K ℓ ht hK hZ f hf hfC hfin
  obtain ⟨𝒰, h𝒰C, hid, hhess⟩ := hdens m t K ℓ ht hK hZ
  have htR : (0 : ℝ) < t := ht
  have hC : MeasurableSet (chamber m ℓ) := measurableSet_chamber
  have hφ := measurable_orderedEigs K
  -- the push-forward of the sector law
  have hmap : (sectorLaw m t K ℓ).map (orderedEigs K) = gibbsOn (chamber m ℓ) 𝒰 := by
    ext A hA
    have hgA : Measurable (A.indicator (1 : (Fin m → ℝ) → ℝ≥0∞)) := measurable_one.indicator hA
    rw [Measure.map_apply hφ hA, ← lintegral_indicator_one (hφ hA),
      lintegral_sectorLaw (g := fun x =>
        (orderedEigs K ⁻¹' A).indicator (1 : (HermCoord m → ℝ) → ℝ≥0∞) x) hK hZ
        (measurable_one.indicator (hφ hA))]
    have hcomp : ∀ x, (orderedEigs K ⁻¹' A).indicator (1 : (HermCoord m → ℝ) → ℝ≥0∞) x =
        A.indicator (1 : (Fin m → ℝ) → ℝ≥0∞) (orderedEigs K x) := fun _ => rfl
    simp_rw [hcomp]
    rw [hid _ hgA, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZ).ne'
        ENNReal.ofReal_ne_top, one_mul, gibbsOn, withDensity_apply _ hA,
      ← lintegral_indicator hA]
    refine lintegral_congr fun lam => ?_
    by_cases h : lam ∈ A <;> simp [h]
  have hprob : IsProbabilityMeasure (gibbsOn (chamber m ℓ) 𝒰) := by
    rw [← hmap]
    have := isProbabilityMeasure_sectorLaw (t := t) hK hZ
    infer_instance
  have hEm : Measurable fun lam => ENNReal.ofReal (weightedEnergy (t : ℝ) f lam) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun j _ => ?_)
    exact ((measurable_fderiv_apply_const ℝ f (Pi.single j 1)).pow_const 2).div
      (measurable_const.add (measurable_const.div ((measurable_pi_apply j).pow_const 2)))
  have hEmap : (∫⁻ x, ENNReal.ofReal (weightedEnergy (t : ℝ) f (orderedEigs K x))
      ∂sectorLaw m t K ℓ) =
      ∫⁻ lam, ENNReal.ofReal (weightedEnergy (t : ℝ) f lam) ∂gibbsOn (chamber m ℓ) 𝒰 := by
    rw [← hmap, lintegral_map hEm hφ]
  rw [evariance_comp_eq_map hφ hf, hmap, hEmap]
  rw [hEmap] at hfin
  have hw : ∀ lam ∈ chamber m ℓ, ∀ j, 0 < (t : ℝ)⁻¹ + 2 / lam j ^ 2 := fun lam hlam j => by
    have := pow_two_pos_of_ne_zero (chamber_ne_zero hlam j)
    positivity
  have hdiag : ∀ lam ∈ chamber m ℓ, ∀ a : Fin m → ℝ,
      ∑ j, ((t : ℝ)⁻¹ + 2 / lam j ^ 2) * a j ^ 2 ≤ iteratedFDeriv ℝ 2 𝒰 lam (fun _ => a) := by
    intro lam hlam a
    refine le_trans ?_ (hhess lam hlam a)
    have hV : 0 ≤ ∑ k, ∑ j, if k < j then (a k - a j) ^ 2 / (lam k - lam j) ^ 2 else 0 :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => by
        split_ifs
        · positivity
        · exact le_rfl
    have hsplit : ∑ j, ((t : ℝ)⁻¹ + 2 / lam j ^ 2) * a j ^ 2 =
        (t : ℝ)⁻¹ * ∑ j, a j ^ 2 + 2 * ∑ j, a j ^ 2 / lam j ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit, curvatureForm]
    linarith
  exact hBL m (chamber m ℓ) (isOpen_chamber ℓ) (convex_chamber ℓ) 𝒰
    (fun lam j => (t : ℝ)⁻¹ + 2 / lam j ^ 2) h𝒰C hw hdiag hprob f hf hfC hfin

/-- **Indexed spectral convexity** from the two named hypotheses: the
eigenvalue density of `K + G_m(t)` (`OrderedEigenDensityStatement`) and the Brascamp–Lieb
inequality on a convex set (`BrascampLiebStatement`). -/
theorem indexedSpectralConvexity_of (hE : OrderedEigenDensityStatement)
    (hBL : BrascampLiebStatement) : IndexedSpectralConvexityStatement :=
  ⟨density_of_orderedEigenDensity hE, variance_of_density (density_of_orderedEigenDensity hE) hBL⟩

end BlockBand.DeterminantScore.SpectralConvexity
