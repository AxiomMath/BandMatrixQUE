module

public import BlockBand.DeterminantScore.NegativeSpreadLaw
public import BlockBand.DeterminantScore.SpectralConvexityHessian

/-!
# The density clause of indexed spectral convexity

`density_of_orderedEigenDensity`: `OrderedEigenDensityStatement` implies the `density` clause of
`IndexedSpectralConvexityStatement`, with
`𝒰 = log Z_ℓ - Σ_j log λ_j² - Σ_{i<j} log(λ_j - λ_i) + Σ_j λ_j²/(2t) - log S`
(the complete spectral density), proving
* that `det(M)² 1{N_-(M) = ℓ}` is `∏_j λ_j² 1{λ ∈ chamber}` almost surely
  (`ofReal_sectorDetSq_eq`, via `det = ∏λ_j` and `N_- = #{j : λ_j < 0}`);
* the density identity with the normalization `Z_ℓ(K)`;
* `𝒰 ∈ C²` on the chamber and the spectral curvature bound: the Hessian of each
  explicit term is computed exactly (`SpectralConvexityHessian`) and that of `-log S` is
  nonnegative by convexity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SpectralConvexity

open MeasureTheory Matrix BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.NegativeSpread
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal

variable {m : ℕ}

/-- The open Weyl chamber `𝒞 = {λ₁ < ⋯ < λ_m}`. -/
def weylChamber (m : ℕ) : Set (Fin m → ℝ) := {lam | StrictMono lam}

/-- The Vandermonde product `Δ(λ) = ∏_{i<j} (λ_j - λ_i)`. -/
def vandermonde (lam : Fin m → ℝ) : ℝ := ∏ i, ∏ j, if i < j then lam j - lam i else 1

/-- **Eigenvalue density of `K + G_m(t)`** (the Hermitian Brownian motion transition density of
Katori–Tanemura, §3.3, (3.10)). For every
`m`, `t > 0` and Hermitian `K` there is `S > 0`, of class `C²` on the Weyl chamber `𝒞`, with
`-log S` convex on `𝒞`, such that the increasing eigenvalues of `K + G_m(t)` have the density
`Δ(λ) e^{-|λ|²/(2t)} S(λ)` on `𝒞` (and do not charge its complement). It is a hypothesis here;
`SpectralChainHolds.orderedEigenDensity_holds` derives it from Prékopa's theorem. -/
structure OrderedEigenDensityStatement : Prop where
  density : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ), 0 < t → K.IsHermitian →
    ∃ S : (Fin m → ℝ) → ℝ, (∀ lam ∈ weylChamber m, 0 < S lam) ∧
      ContDiffOn ℝ 2 S (weylChamber m) ∧
      ConvexOn ℝ (weylChamber m) (fun lam => -Real.log (S lam)) ∧
      ∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
        ∫⁻ x, g (orderedEigs K x) ∂hermGaussian m t =
          ∫⁻ lam in weylChamber m, ENNReal.ofReal (vandermonde lam *
            Real.exp (-(∑ j, lam j ^ 2) / (2 * (t : ℝ))) * S lam) * g lam

/-!
### Chambers
-/

theorem isOpen_weylChamber : IsOpen (weylChamber m) := by
  have hset : weylChamber m =
      ⋂ i : Fin m, ⋂ j : Fin m, {lam : Fin m → ℝ | i < j → lam i < lam j} := by
    ext lam
    simp only [weylChamber, StrictMono, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  by_cases hij : i < j
  · simpa [hij] using isOpen_lt (continuous_apply i) (continuous_apply j)
  · simp [hij]

theorem isOpen_chamber (ℓ : ℕ) : IsOpen (chamber m ℓ) := by
  have hset : chamber m ℓ = weylChamber m ∩
      ⋂ k : Fin m, ({lam : Fin m → ℝ | k.val < ℓ → lam k < 0} ∩
        {lam : Fin m → ℝ | ℓ ≤ k.val → 0 < lam k}) := by
    ext lam
    simp only [chamber, weylChamber, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine isOpen_weylChamber.inter (isOpen_iInter_of_finite fun k => IsOpen.inter ?_ ?_)
  · by_cases hk : k.val < ℓ
    · simpa [hk] using isOpen_lt (continuous_apply k) continuous_const
    · simp [hk]
  · by_cases hk : ℓ ≤ k.val
    · simpa [hk] using isOpen_lt continuous_const (continuous_apply k)
    · simp [hk]

theorem chamber_subset_weylChamber (ℓ : ℕ) : chamber m ℓ ⊆ weylChamber m := fun _ h => h.1

theorem chamber_ne_zero {ℓ : ℕ} {lam : Fin m → ℝ} (h : lam ∈ chamber m ℓ) (k : Fin m) :
    lam k ≠ 0 := by
  by_cases hk : k.val < ℓ
  · exact ((h.2 k).1 hk).ne
  · exact ((h.2 k).2 (not_lt.1 hk)).ne'

theorem vandermonde_pos {lam : Fin m → ℝ} (h : lam ∈ weylChamber m) : 0 < vandermonde lam := by
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  split_ifs with hij
  · exact sub_pos.2 (h hij)
  · exact one_pos

/-!
### Determinant and inertia through the increasing eigenvalues
-/

theorem exists_equiv_freshEigenvalue {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian) :
    ∃ e : Fin m ≃ Fin m, ∀ k, freshEigenvalue M k = hM.eigenvalues (e k) := by
  refine ⟨((finCongr (Fintype.card_fin m).symm).trans Fin.revPerm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m)))), fun k => ?_⟩
  simp [freshEigenvalue, BlockBand.Model.Construction.rawIncreasingEigenvalue, hM,
    BlockBand.Foundations.Spectral.increasingEigenvalue, Matrix.IsHermitian.eigenvalues]

theorem det_eq_prod_freshEigenvalue {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian) :
    M.det = ∏ k, ((freshEigenvalue M k : ℝ) : ℂ) := by
  obtain ⟨e, he⟩ := exists_equiv_freshEigenvalue hM
  rw [hM.det_eq_prod_eigenvalues]
  simp_rw [he]
  exact (Equiv.prod_comp e (fun i => ((hM.eigenvalues i : ℝ) : ℂ))).symm

theorem negativeCount_eq_card_freshEigenvalue {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : M.IsHermitian) :
    negativeCount M = (Finset.univ.filter fun k => freshEigenvalue M k < 0).card := by
  obtain ⟨e, he⟩ := exists_equiv_freshEigenvalue hM
  rw [negativeCount_eq_sum hM, Finset.card_filter]
  simp_rw [he]
  exact (Equiv.sum_comp e (fun i => if hM.eigenvalues i < 0 then 1 else 0)).symm

/-- For monotone `λ` without zero entry, `λ_k < 0 ↔ k < #{j : λ_j < 0}`. -/
theorem neg_iff_lt_card {lam : Fin m → ℝ} (hmono : Monotone lam) (hne : ∀ k, lam k ≠ 0)
    (k : Fin m) : lam k < 0 ↔ k.val < (Finset.univ.filter fun j => lam j < 0).card := by
  constructor
  · intro hk
    have hsub : Finset.Iic k ⊆ Finset.univ.filter fun j => lam j < 0 := by
      intro j hj
      simp only [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (hmono hj) hk
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hk
    by_contra hneg
    have hpos : 0 < lam k := lt_of_le_of_ne (not_lt.1 hneg) (hne k).symm
    have hsub : (Finset.univ.filter fun j => lam j < 0) ⊆ Finset.Iio k := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      by_contra hjk
      exact absurd (lt_of_lt_of_le hpos (hmono (not_lt.1 hjk))) (not_lt.2 hj.le)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- `det(M)² 1{N_-(M) = ℓ} = ∏_j λ_j² 1{λ ∈ chamber}` at every `x` whose increasing eigenvalues are
simple (`ℓ ≤ m`). -/
theorem ofReal_sectorDetSq_eq {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) {ℓ : ℕ}
    (hℓ : ℓ ≤ m) {x : HermCoord m → ℝ} (hx : orderedEigs K x ∈ weylChamber m) :
    ENNReal.ofReal (sectorDetSq K ℓ x).re =
      (chamber m ℓ).indicator (fun lam => ENNReal.ofReal (∏ j, lam j ^ 2)) (orderedEigs K x) := by
  set lam := orderedEigs K x with hlam
  have hM := isHermitian_add_hermOfCoord hK x
  have hdet : (K + hermOfCoord x).det = ∏ k, ((lam k : ℝ) : ℂ) := det_eq_prod_freshEigenvalue hM
  have hcount : negativeCount (K + hermOfCoord x) =
      (Finset.univ.filter fun k => lam k < 0).card := negativeCount_eq_card_freshEigenvalue hM
  have hmono : Monotone lam := (show StrictMono lam from hx).monotone
  have hre : ((K + hermOfCoord x).det ^ 2).re = ∏ j, lam j ^ 2 := by
    rw [hdet, ← Complex.ofReal_prod, ← Complex.ofReal_pow, Complex.ofReal_re, Finset.prod_pow]
  by_cases hc : lam ∈ chamber m ℓ
  · rw [Set.indicator_of_mem hc]
    have hne := chamber_ne_zero hc
    have hiff : ∀ k : Fin m, k.val < (Finset.univ.filter fun j => lam j < 0).card ↔ k.val < ℓ := by
      intro k
      rw [← neg_iff_lt_card hmono hne k]
      constructor
      · intro hk
        by_contra h'
        exact absurd hk (not_lt.2 ((hc.2 k).2 (not_lt.1 h')).le)
      · exact (hc.2 k).1
    have hp : (Finset.univ.filter fun j => lam j < 0).card ≤ m := by
      simpa using Finset.card_le_univ (Finset.univ.filter fun j => lam j < 0)
    have hcard : (Finset.univ.filter fun j => lam j < 0).card = ℓ := by
      set p := (Finset.univ.filter fun j => lam j < 0).card
      rcases lt_trichotomy p ℓ with h | h | h
      · exact absurd ((hiff ⟨p, lt_of_lt_of_le h hℓ⟩).2 h) (lt_irrefl _)
      · exact h
      · exact absurd ((hiff ⟨ℓ, lt_of_lt_of_le h hp⟩).1 h) (lt_irrefl _)
    have hs : InSector K ℓ x := by rw [InSector, hcount, hcard]
    rw [sectorDetSq]
    simp only [hs, ↓reduceIte]
    rw [hre]
  · rw [Set.indicator_of_notMem hc, ENNReal.ofReal_eq_zero]
    unfold sectorDetSq
    split_ifs with hs
    · by_cases hz : ∏ j, lam j = 0
      · have : (K + hermOfCoord x).det = 0 := by
          rw [hdet, ← Complex.ofReal_prod, hz, Complex.ofReal_zero]
        simp [this]
      · exfalso
        have hne : ∀ k, lam k ≠ 0 := fun k hk =>
          hz (Finset.prod_eq_zero (Finset.mem_univ k) hk)
        rw [InSector, hcount] at hs
        refine hc ⟨hx, fun k => ⟨fun hk => ?_, fun hk => ?_⟩⟩
        · exact (neg_iff_lt_card hmono hne k).2 (hs ▸ hk)
        · have h1 : ¬ lam k < 0 := fun h => by
            have := (neg_iff_lt_card hmono hne k).1 h
            omega
          exact lt_of_le_of_ne (not_lt.1 h1) (hne k).symm
    · simp

/-!
### Attainable sectors and the representation
-/

/-- An attainable sector has `ℓ ≤ m`. -/
theorem le_of_sectorMass_pos {t : ℝ≥0} {K : Matrix (Fin m) (Fin m) ℂ} {ℓ : ℕ}
    (hK : K.IsHermitian) (hZ : 0 < (sectorMass m t K ℓ).re) : ℓ ≤ m := by
  by_contra h
  have h0 : ∀ x, sectorDetSq K ℓ x = 0 := by
    intro x
    have hns : ¬ InSector K ℓ x := by
      intro hs
      rw [InSector, negativeCount_eq_card_freshEigenvalue (isHermitian_add_hermOfCoord hK x)]
        at hs
      have := Finset.card_le_univ
        (Finset.univ.filter fun k => freshEigenvalue (K + hermOfCoord x) k < 0)
      simp only [Fintype.card_fin] at this
      omega
    simp [sectorDetSq, hns]
  simp [sectorMass, h0] at hZ

/-- A representation on the Weyl chamber forces the increasing eigenvalues to be a.s. simple. -/
theorem ae_mem_weylChamber_of_rep {μ : Measure (HermCoord m → ℝ)}
    {K : Matrix (Fin m) (Fin m) ℂ} {D : (Fin m → ℝ) → ℝ≥0∞}
    (hrep : ∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (orderedEigs K x) ∂μ = ∫⁻ lam in weylChamber m, D lam * g lam) :
    ∀ᵐ x ∂μ, orderedEigs K x ∈ weylChamber m := by
  have hW : MeasurableSet (weylChamber m) := isOpen_weylChamber.measurableSet
  set G : (Fin m → ℝ) → ℝ≥0∞ := (weylChamber m)ᶜ.indicator 1 with hGdef
  have hGm : Measurable G := measurable_one.indicator hW.compl
  have hzero : ∫⁻ lam in weylChamber m, D lam * G lam = 0 := by
    rw [setLIntegral_congr_fun hW (g := fun _ => (0 : ℝ≥0∞))
      (fun lam hlam => by simp [hGdef, hlam])]
    simp
  rw [ae_iff]
  have hpre : {x | ¬ orderedEigs K x ∈ weylChamber m} = orderedEigs K ⁻¹' (weylChamber m)ᶜ :=
    rfl
  have hind : ∀ x, (orderedEigs K ⁻¹' (weylChamber m)ᶜ).indicator 1 x = G (orderedEigs K x) :=
    fun x => rfl
  rw [hpre, ← lintegral_indicator_one (measurable_orderedEigs K hW.compl)]
  simp_rw [hind]
  rw [hrep G hGm, hzero]

/-!
### The `density` clause
-/

/-- **The `density` clause of indexed spectral convexity**, from the eigenvalue density
`OrderedEigenDensityStatement`. Exactly the field `IndexedSpectralConvexityStatement.density`. -/
theorem density_of_orderedEigenDensity (hE : OrderedEigenDensityStatement) :
    ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
    K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
    ∃ 𝒰 : (Fin m → ℝ) → ℝ, ContDiffOn ℝ 2 𝒰 (chamber m ℓ) ∧
      (∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
        (∫⁻ x, ENNReal.ofReal (sectorDetSq K ℓ x).re * g (orderedEigs K x) ∂hermGaussian m t) =
          ENNReal.ofReal (sectorMass m t K ℓ).re *
            ∫⁻ lam in chamber m ℓ, ENNReal.ofReal (Real.exp (-𝒰 lam)) * g lam) ∧
      ∀ lam ∈ chamber m ℓ, ∀ a : Fin m → ℝ,
        curvatureForm (t : ℝ) lam a ≤ iteratedFDeriv ℝ 2 𝒰 lam (fun _ => a) := by
  intro m t K ℓ ht hK hZ
  obtain ⟨S, hSpos, hSC, hSconv, hrep⟩ := hE.density m t K ht hK
  have hℓ := le_of_sectorMass_pos hK hZ
  set Z := (sectorMass m t K ℓ).re with hZdef
  have htR : (0 : ℝ) < t := ht
  let P : Fin m → (Fin m → ℝ) →L[ℝ] ℝ := fun j => ContinuousLinearMap.proj j
  have hP : ∀ j (lam : Fin m → ℝ), P j lam = lam j := fun _ _ => rfl
  let f1 : Fin m → (Fin m → ℝ) → ℝ := fun j lam => -Real.log ((P j lam) ^ 2)
  let B : Fin m → Fin m → (Fin m → ℝ) → ℝ := fun i j =>
    if i < j then (fun lam => -Real.log ((P j - P i) lam)) else 0
  let f2 : Fin m → (Fin m → ℝ) → ℝ := fun i lam => ∑ j, B i j lam
  let f3 : Fin m → (Fin m → ℝ) → ℝ := fun j lam => (2 * (t : ℝ))⁻¹ * (P j lam) ^ 2
  let A0 : (Fin m → ℝ) → ℝ := fun _ => Real.log Z
  let A1 : (Fin m → ℝ) → ℝ := fun lam => ∑ j, f1 j lam
  let A2 : (Fin m → ℝ) → ℝ := fun lam => ∑ i, f2 i lam
  let A3 : (Fin m → ℝ) → ℝ := fun lam => ∑ j, f3 j lam
  let A4 : (Fin m → ℝ) → ℝ := fun lam => -Real.log (S lam)
  refine ⟨A0 + A1 + A2 + A3 + A4, ?_, ?_, ?_⟩
  -- smoothness of the pieces on the chamber
  all_goals
    have hB : ∀ i j (lam : Fin m → ℝ), B i j lam =
        if i < j then -Real.log (lam j - lam i) else 0 := by
      intro i j lam
      by_cases hij : i < j <;> simp [B, hij, P]
    have hf1 : ∀ lam ∈ chamber m ℓ, ∀ j, ContDiffAt ℝ 2 (f1 j) lam := fun lam hlam j =>
      (((P j).contDiff.pow 2).contDiffAt.log (pow_ne_zero 2 (chamber_ne_zero hlam j))).neg
    have hBc : ∀ lam ∈ chamber m ℓ, ∀ i j, ContDiffAt ℝ 2 (B i j) lam := by
      intro lam hlam i j
      by_cases hij : i < j
      · have hne : (P j - P i) lam ≠ 0 := by
          change lam j - lam i ≠ 0
          exact (sub_pos.2 (hlam.1 hij)).ne'
        simpa [B, hij] using ((P j - P i).contDiff.contDiffAt.log hne).neg
      · simp only [B, hij, ↓reduceIte]
        exact contDiff_zero_fun.contDiffAt
    have hf2 : ∀ lam ∈ chamber m ℓ, ∀ i, ContDiffAt ℝ 2 (f2 i) lam := fun lam hlam i =>
      ContDiffAt.sum fun j _ => hBc lam hlam i j
    have hf3 : ∀ lam, ∀ j, ContDiffAt ℝ 2 (f3 j) lam := fun lam j =>
      (contDiff_const.mul ((P j).contDiff.pow 2)).contDiffAt
    have hA4 : ∀ lam ∈ chamber m ℓ, ContDiffAt ℝ 2 A4 lam := fun lam hlam =>
      (((hSC.contDiffAt (isOpen_weylChamber.mem_nhds (chamber_subset_weylChamber ℓ hlam)))).log
        (hSpos lam (chamber_subset_weylChamber ℓ hlam)).ne').neg
    have hA1 : ∀ lam ∈ chamber m ℓ, ContDiffAt ℝ 2 A1 lam := fun lam hlam =>
      ContDiffAt.sum fun j _ => hf1 lam hlam j
    have hA2 : ∀ lam ∈ chamber m ℓ, ContDiffAt ℝ 2 A2 lam := fun lam hlam =>
      ContDiffAt.sum fun i _ => hf2 lam hlam i
    have hA3 : ∀ lam, ContDiffAt ℝ 2 A3 lam := fun lam =>
      ContDiffAt.sum fun j _ => hf3 lam j
    have hA0 : ∀ lam, ContDiffAt ℝ 2 A0 lam := fun _ => contDiffAt_const
  · intro lam hlam
    exact ((((hA0 lam).add (hA1 lam hlam)).add (hA2 lam hlam)).add (hA3 lam)).add
      (hA4 lam hlam) |>.contDiffWithinAt
  · intro g hg
    have hC : MeasurableSet (chamber m ℓ) := measurableSet_chamber
    have hpos : ∀ lam ∈ chamber m ℓ, 0 < ∏ j, lam j ^ 2 ∧ 0 < vandermonde lam *
        Real.exp (-(∑ j, lam j ^ 2) / (2 * (t : ℝ))) * S lam := fun lam hlam =>
      ⟨Finset.prod_pos fun j _ => pow_two_pos_of_ne_zero (chamber_ne_zero hlam j),
        mul_pos (mul_pos (vandermonde_pos (chamber_subset_weylChamber ℓ hlam)) (Real.exp_pos _))
          (hSpos lam (chamber_subset_weylChamber ℓ hlam))⟩
    have hval : ∀ lam ∈ chamber m ℓ, Real.exp (-((A0 + A1 + A2 + A3 + A4) lam)) =
        Z⁻¹ * ((∏ j, lam j ^ 2) *
          (vandermonde lam * Real.exp (-(∑ j, lam j ^ 2) / (2 * (t : ℝ))) * S lam)) := by
      intro lam hlam
      have hne := chamber_ne_zero hlam
      have hWl := chamber_subset_weylChamber ℓ hlam
      obtain ⟨hPi, hVES⟩ := hpos lam hlam
      have hV := vandermonde_pos hWl
      have hS := hSpos lam hWl
      have hfac : ∀ i j : Fin m, (if i < j then lam j - lam i else 1) ≠ 0 := by
        intro i j
        split_ifs with hij
        · exact (sub_pos.2 (hWl hij)).ne'
        · exact one_ne_zero
      have hlogV : Real.log (vandermonde lam) =
          ∑ i, ∑ j, if i < j then Real.log (lam j - lam i) else 0 := by
        rw [vandermonde, Real.log_prod (fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => hfac i j)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.log_prod (fun j _ => hfac i j)]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      have hlogP : Real.log (∏ j, lam j ^ 2) = ∑ j, Real.log (lam j ^ 2) :=
        Real.log_prod (fun j _ => pow_ne_zero 2 (hne j))
      have hU : (A0 + A1 + A2 + A3 + A4) lam = -Real.log (Z⁻¹ * ((∏ j, lam j ^ 2) *
          (vandermonde lam * Real.exp (-(∑ j, lam j ^ 2) / (2 * (t : ℝ))) * S lam))) := by
        rw [Real.log_mul (inv_ne_zero hZ.ne') (mul_pos hPi hVES).ne', Real.log_inv,
          Real.log_mul hPi.ne' hVES.ne', Real.log_mul (mul_pos hV (Real.exp_pos _)).ne' hS.ne',
          Real.log_mul hV.ne' (Real.exp_pos _).ne', Real.log_exp, hlogV, hlogP]
        simp only [Pi.add_apply, A0, A1, A2, A3, A4, f1, f2, f3, hB, hP]
        have h2 : (∑ i, ∑ j, if i < j then -Real.log (lam j - lam i) else (0 : ℝ)) =
            -∑ i, ∑ j, if i < j then Real.log (lam j - lam i) else 0 := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
        have h3 : ∑ j, (2 * (t : ℝ))⁻¹ * lam j ^ 2 = (∑ j, lam j ^ 2) / (2 * (t : ℝ)) := by
          rw [← Finset.mul_sum, div_eq_inv_mul]
        rw [h2, h3, Finset.sum_neg_distrib]
        ring
      rw [hU, neg_neg, Real.exp_log (mul_pos (inv_pos.2 hZ) (mul_pos hPi hVES))]
    set D : (Fin m → ℝ) → ℝ≥0∞ := fun lam => ENNReal.ofReal (vandermonde lam *
      Real.exp (-(∑ j, lam j ^ 2) / (2 * (t : ℝ))) * S lam) with hDdef
    have hae := ae_mem_weylChamber_of_rep (μ := hermGaussian m t) (D := D) hrep
    set F : (Fin m → ℝ) → ℝ≥0∞ := fun lam =>
      (chamber m ℓ).indicator (fun lam => ENNReal.ofReal (∏ j, lam j ^ 2)) lam * g lam with hFdef
    have hFm : Measurable F :=
      ((ENNReal.measurable_ofReal.comp (continuous_finsetProd _ fun j _ =>
        (continuous_apply j).pow 2).measurable).indicator hC).mul hg
    rw [lintegral_congr_ae (g := fun x => F (orderedEigs K x)) (hae.mono fun x hx => by
      rw [ofReal_sectorDetSq_eq hK hℓ hx]), hrep F hFm,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hind : ∀ lam, ENNReal.ofReal (vandermonde lam *
        Real.exp (-(∑ j, lam j ^ 2) / (2 * (t : ℝ))) * S lam) * F lam = (chamber m ℓ).indicator
        (fun lam => ENNReal.ofReal (vandermonde lam *
          Real.exp (-(∑ j, lam j ^ 2) / (2 * (t : ℝ))) * S lam) *
          (ENNReal.ofReal (∏ j, lam j ^ 2) * g lam)) lam := by
      intro lam
      by_cases h : lam ∈ chamber m ℓ <;> simp [hFdef, h]
    simp_rw [hind]
    rw [lintegral_indicator hC, Measure.restrict_restrict hC,
      Set.inter_eq_left.2 (chamber_subset_weylChamber ℓ)]
    refine setLIntegral_congr_fun hC fun lam hlam => ?_
    obtain ⟨hPi, hVES⟩ := hpos lam hlam
    have hW : ∀ W : ℝ, ENNReal.ofReal Z * ENNReal.ofReal (Z⁻¹ * W) = ENNReal.ofReal W := by
      intro W
      rw [← ENNReal.ofReal_mul hZ.le, ← mul_assoc, mul_inv_cancel₀ hZ.ne', one_mul]
    rw [hval lam hlam, ← mul_assoc (ENNReal.ofReal Z), hW, ENNReal.ofReal_mul hPi.le]
    ring
  · intro lam hlam a
    have hne := chamber_ne_zero hlam
    have h01 : ContDiffAt ℝ 2 (A0 + A1) lam := (hA0 lam).add (hA1 lam hlam)
    have h012 : ContDiffAt ℝ 2 (A0 + A1 + A2) lam := h01.add (hA2 lam hlam)
    have h0123 : ContDiffAt ℝ 2 (A0 + A1 + A2 + A3) lam := h012.add (hA3 lam)
    rw [iteratedFDeriv_add_apply h0123 (hA4 lam hlam), iteratedFDeriv_add_apply h012 (hA3 lam),
      iteratedFDeriv_add_apply h01 (hA2 lam hlam), iteratedFDeriv_add_apply (hA0 lam)
      (hA1 lam hlam)]
    simp only [_root_.add_apply]
    have e0 : iteratedFDeriv ℝ 2 A0 lam (fun _ => a) = 0 := by
      simp [A0, iteratedFDeriv_const_of_ne (show (2 : ℕ) ≠ 0 by norm_num)]
    have e1 : iteratedFDeriv ℝ 2 A1 lam (fun _ => a) = ∑ j, 2 * (a j ^ 2 / lam j ^ 2) := by
      rw [show A1 = fun lam => ∑ j ∈ Finset.univ, f1 j lam from rfl,
        iteratedFDeriv_fun_sum_apply (fun j _ => hf1 lam hlam j), _root_.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact iteratedFDeriv_two_neg_log_sq_clm (P j) (hne j) a
    have e2 : iteratedFDeriv ℝ 2 A2 lam (fun _ => a) =
        ∑ i, ∑ j, if i < j then (a j - a i) ^ 2 / (lam j - lam i) ^ 2 else 0 := by
      rw [show A2 = fun lam => ∑ i ∈ Finset.univ, f2 i lam from rfl,
        iteratedFDeriv_fun_sum_apply (fun i _ => hf2 lam hlam i), _root_.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show f2 i = fun lam => ∑ j ∈ Finset.univ, B i j lam from rfl,
        iteratedFDeriv_fun_sum_apply (fun j _ => hBc lam hlam i j), _root_.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i < j
      · have hne' : (P j - P i) lam ≠ 0 := by
          change lam j - lam i ≠ 0
          exact (sub_pos.2 (hlam.1 hij)).ne'
        simp only [B, hij, ↓reduceIte]
        rw [iteratedFDeriv_two_neg_log_clm (P j - P i) hne' a]
        simp [P]
      · simp only [B, hij, ↓reduceIte]
        have : ((0 : (Fin m → ℝ) → ℝ)) = fun _ => (0 : ℝ) := rfl
        rw [this, iteratedFDeriv_const_of_ne (show (2 : ℕ) ≠ 0 by norm_num)]
        rfl
    have e3 : iteratedFDeriv ℝ 2 A3 lam (fun _ => a) = ∑ j, 2 * (2 * (t : ℝ))⁻¹ * a j ^ 2 := by
      rw [show A3 = fun lam => ∑ j ∈ Finset.univ, f3 j lam from rfl,
        iteratedFDeriv_fun_sum_apply (fun j _ => hf3 lam j), _root_.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact iteratedFDeriv_two_sq_clm (P j) _ lam a
    have e4 : 0 ≤ iteratedFDeriv ℝ 2 A4 lam (fun _ => a) :=
      iteratedFDeriv_two_nonneg_of_convexOn
        (isOpen_weylChamber.mem_nhds (chamber_subset_weylChamber ℓ hlam)) hSconv (hA4 lam hlam) a
    rw [e0, e1, e2, e3]
    have c1 : ∑ j, 2 * (a j ^ 2 / lam j ^ 2) = 2 * ∑ j, a j ^ 2 / lam j ^ 2 := by
      rw [Finset.mul_sum]
    have c2 : (∑ k, ∑ j, if k < j then (a k - a j) ^ 2 / (lam k - lam j) ^ 2 else 0) =
        ∑ i, ∑ j, if i < j then (a j - a i) ^ 2 / (lam j - lam i) ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [show (a k - a j) ^ 2 = (a j - a k) ^ 2 by ring,
          show (lam k - lam j) ^ 2 = (lam j - lam k) ^ 2 by ring]
      · rfl
    have c3 : ∑ j, 2 * (2 * (t : ℝ))⁻¹ * a j ^ 2 = (t : ℝ)⁻¹ * ∑ j, a j ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [curvatureForm, c1, c2, c3]
    linarith

end BlockBand.DeterminantScore.SpectralConvexity
