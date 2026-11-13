module
public import BlockBand.Critical.PhysicalProfiles
public import BlockBand.Model.Construction.SpectralFiniteRealization

/-!
# Source readback for the ordered physical eigenpairs

For the measurable increasing eigenpair selector of the physical Gaussian ring, almost
surely every eigenvalue rank has a nonzero energy partial, and the source ratios recover
the quadratic forms of the selected eigenvector, hence the integrals of continuous circle
tests against its block-mass profile.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Critical
open MeasureTheory
open BlockBand.Model.Construction BlockBand.Foundations.Spectral
open scoped Matrix BigOperators

/-- Arbitrary noncommuting complex source quadratics are invariant under unit
complex phase; this retains signed and complex matrix sources. -/
theorem quadratic_source_unit_phase {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℂ) (v : ι → ℂ) (z : ℂ) (hz : ‖z‖=1) :
    dotProduct (star (z • v)) (Q *ᵥ (z • v)) = dotProduct (star v) (Q *ᵥ v) := by
  have hunit : star z*z=1 := by
    rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hz]
    norm_num
  rw [Matrix.mulVec_smul,star_smul,dotProduct_smul,smul_dotProduct]
  simp only [smul_eq_mul]
  rw [← mul_assoc,mul_comm z (star z),hunit,one_mul]

/-- The physical measurable increasing selector has exactly the spectral
basis quadratic for every complex source, by unit-phase invariance. -/
theorem physicalOrdered_source_quadratic {p : BlockBand.Parameters}
    (H : p.SiteMatrix) (hH : H.IsHermitian) (hsep : H.charpoly.Separable)
    (α : Fin p.N) (Q : p.SiteMatrix) :
    dotProduct (star (physicalOrderedEigenvector p H α))
      (Q *ᵥ physicalOrderedEigenvector p H α) =
        dotProduct (star ⇑(hH.eigenvectorBasis (increasingIndex (physicalSpectralRank p α))))
          (Q *ᵥ ⇑(hH.eigenvectorBasis (increasingIndex (physicalSpectralRank p α)))) := by
  have hsimple := orderedEigenvalue_injective_of_separable (⟨H,hH⟩ : HermitianMatrix p.Site) hsep
  obtain ⟨z,hz,he⟩ := orderedColumnSelection_eq_phase (physicalSpectralRank p α)
    (⟨H,hH⟩ : HermitianMatrix p.Site) hsimple
  have hv : physicalOrderedEigenvector p H α =
      z • ⇑(hH.eigenvectorBasis (increasingIndex (physicalSpectralRank p α))) := by
    funext x
    unfold physicalOrderedEigenvector
    rw [rawOrderedColumnSelection_eq _ H hH,congrFun he x]
    simp only [Pi.smul_apply,increasingEigenvector,increasingEigenbasis_apply]
  rw [hv,quadratic_source_unit_phase Q _ z hz]

/-- Profile source quadratics are integrals against the `Torus` probability profile of
the constructed spectral realization. -/
theorem physicalOrdered_profile_source_integral {p : BlockBand.Parameters}
    (H : p.SiteMatrix) (hH : H.IsHermitian) (hsep : H.charpoly.Separable)
    (α : Fin p.N) (q : ContinuousMap Torus ℝ) :
    dotProduct (star (physicalOrderedEigenvector p H α))
      (p.profileSourceMatrix q *ᵥ physicalOrderedEigenvector p H α) =
        ((∫ r,q r ∂(physicalOrderedProfile p H α : Measure Torus) : ℝ) : ℂ) := by
  rw [p.quadratic_profileSourceMatrix,physicalOrderedProfile_integral p H hH hsep α q]
  rfl

/-- Under the Gaussian ring law, almost surely every increasing rank has a nonzero
energy partial and exact source ratios for all complex sources. -/
theorem physicalOrdered_source_readback_ae {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (E : ℝ) {m : ℕ}
    (Q : Fin (m+1) → p.SiteMatrix) (hQ : Q 0=1) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∃ hA : (H-(E:ℂ) • (1:p.SiteMatrix)).det ≠ 0,
      ∀ α : Fin p.N,
        let A := H-(E:ℂ) • (1:p.SiteMatrix)
        let z := -(p.W:ℂ)^2*((physicalOrderedEigenvalue p H α:ℂ)-(E:ℂ))
        finiteSourcePartial A Q p.W hA z 0 ≠ 0 ∧
          ∀ a : Fin (m+1), finiteSourcePartial A Q p.W hA z a /
            finiteSourcePartial A Q p.W hA z 0 =
              dotProduct (star (physicalOrderedEigenvector p H α))
                (Q a *ᵥ physicalOrderedEigenvector p H α) := by
  filter_upwards [model.isPhysical.1,model.ae_charpoly_separable,
    model.ae_all_eigenpair_source_readback E Q hQ] with H hH hsep hread
  obtain ⟨hH',hA,hr⟩ := hread
  have he (α : Fin p.N) : physicalOrderedEigenvalue p H α=
      hH'.eigenvalues (increasingIndex (physicalSpectralRank p α)) := by
    unfold physicalOrderedEigenvalue
    rw [rawIncreasingEigenvalue_eq _ H hH',eigenvalue_increasingIndex]
  refine ⟨hA,fun α => ?_⟩
  dsimp only
  rw [he α]
  refine ⟨(hr _).1,fun a => ?_⟩
  rw [(hr _).2 a,physicalOrdered_source_quadratic H hH' hsep α (Q a)]

/-- Exact source ratios recover every continuous physical circle test in the
constructed full finite realization, simultaneously in all increasing ranks. -/
theorem physicalOrdered_profile_readback_ae {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (E : ℝ) {m : ℕ}
    (q : Fin (m+1) → ContinuousMap Torus ℝ)
    (hq : q 0=ContinuousMap.const Torus (1:ℝ)) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∃ hA : (H-(E:ℂ) • (1:p.SiteMatrix)).det ≠ 0,
      ∀ α : Fin p.N,
        let Q := fun a => p.profileSourceMatrix (q a)
        let A := H-(E:ℂ) • (1:p.SiteMatrix)
        let z := -(p.W:ℂ)^2*((physicalOrderedEigenvalue p H α:ℂ)-(E:ℂ))
        finiteSourcePartial A Q p.W hA z 0 ≠ 0 ∧
          ∀ a : Fin (m+1), finiteSourcePartial A Q p.W hA z a /
            finiteSourcePartial A Q p.W hA z 0 =
              ((∫ r,q a r ∂((constructSpectralRealization p model).profile H α : Measure Torus):ℝ):ℂ) := by
  have hQ : (fun a => p.profileSourceMatrix (q a)) 0=1 := by
    change p.profileSourceMatrix (q 0)=1
    rw [hq]
    exact p.profileSourceMatrix_one
  filter_upwards [model.isPhysical.1,model.ae_charpoly_separable,
    physicalOrdered_source_readback_ae model E (fun a => p.profileSourceMatrix (q a)) hQ]
    with H hH hsep hread
  obtain ⟨hA,hr⟩ := hread
  refine ⟨hA,fun α => ⟨(hr α).1,fun a => ?_⟩⟩
  rw [(hr α).2 a]
  exact physicalOrdered_profile_source_integral H hH hsep α (q a)

end BlockBand.Critical
