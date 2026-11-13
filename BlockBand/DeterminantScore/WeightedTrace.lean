module

public import BlockBand.DeterminantScore.WeightedTracePair
public import BlockBand.DeterminantScore.WeightedTraceArith

/-!
# The physical weighted trace bound

`physicalWeightedTrace_holds (hC : CoareaContract) (hLW : PhysicalLocalWindowStatement)
(hSR : SelectedResolventStatement) : PhysicalWeightedTraceStatement`, the first step of the
physical real loop, with constant `C W^{49/50}` (exponent bookkeeping in `w = W^{1/100}`: every
term is `O(W^{98/100})`).

## Proof outline

Parameters: `η = W^{-3/5}` (`γ = 2/5` in the local window), `L₀ = W^{1/4}`, `ε = 1/100`,
failure power `D = 6`. Frame coordinates: `R = M⁻¹`, `M = K + G'`, `R_A = U_vRU_v*`.

* In frame coordinates, `Tr G_dR - sE Tr R - (sd - 1)` equals `d(1-s) - Re Tr(K₀ + sE)R_A`
  (`weightedTraceError_eq`; `A = U_vMU_v*` `schurA_rec_eq`, `R_A = A⁺`
  `isMoorePenrose_frame`, completeness `frame_complete`).
* The physical local window is applied to the dilated cutoff `K_{0,L₀}/L₀` (`WeightedTraceCutoff`:
  `dilatedCutoff`, `isSpectralTest_dilatedCutoff`, `isWindowObservable_cutoff`); the bounds
  `‖K₀u‖ ≤ |λ| + ‖G_d‖`, `|u*(K₀ - K_{0,L₀})u| ≤ C/L₀`, the same tail bound for the covariance
  trace, and the unbounded-observable eigenstate thermalization give `eth_unbounded`, with the
  centre `g(λ) = d⁻¹ Tr K₀Γ_E(λ) = windowCenter K₀ K₀ s λ`.
* The resolvent estimates at the selected energy (averaged local law, Gaussian integration by
  parts and `L^p` Poincaré on the energy and rank-one grids, regularity of `m_E`, the certificate
  `m_E(0) = m_sc(E) + O(W^{-1+ε})`, and `|g'(λ)| ≤ C`, `g(0) = -sE + O(W^{-1+ε})`) are not
  consequences of the statement of the physical local window. They form the named hypothesis
  **`SelectedResolventStatement`** below, stated in the format of `PhysicalLocalWindowStatement`
  (an event of small pair-law probability outside which the estimates hold at every selected bulk
  energy `E = λ_α`).
* The identity `K₀R_η = I + iηR_η - G_dR_η` gives
  `Tr(K₀ - g(0)) Re R_η = d(1 - s|m_E(0)|²) + O(W^{9/10+2ε} + dη)`, and `|m_sc(E)| = 1`
  (`trace_smoothed_eq`, `smoothed_scalar_bound`, `matchedA_norm`).
* Score unsmoothing with the unbounded-observable bound and the Poisson bound, and the
  replacement of `g(0)` by `-sE`: `good_bound` (from
  `ScoreUnsmoothing.score_unsmoothing_of_unit_eigenvectors_nearSum`; the Poisson bound comes from
  the local window), with exponents in `good_arith`.
* The physical column bound controls the first term's expectation (`physicalColumn_holds`,
  `q = 2`, with `‖R‖ ≤ (W^{24/25} + W^{-26/25}‖R‖²)/2`).
* On the exceptional events, `Tr K₀R = d - 1 - Tr G_dR` gives the trivial bound
  `weightedTraceError_le_trivial`; Young's inequality (`bad_arith`) replaces Hölder, with the
  Gaussian norm event and moments (`WeightedTracePair`) and the events transferred by
  `pairExpect_hull_eq` (`CoareaContract.pairLaw_formula`). Small `W` (`η > δ'`) is also treated
  as exceptional.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeightedTrace

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector BlockBand.DeterminantScore.RealLoop
open BlockBand.DeterminantScore.MinorTailInverse BlockBand.DeterminantScore.PhysicalColumn
open BlockBand.DeterminantScore.GUENormTail BlockBand.DeterminantScore.ScoreUnsmoothing
open BlockBand.DeterminantScore.MinorTail BlockBand.DeterminantScore.ScoreMoments
open BlockBand.LocalWindow
open scoped NNReal ENNReal ComplexConjugate Matrix.Norms.L2Operator

/-- **Selected-energy resolvent inputs of the physical weighted trace bound**, the named
hypothesis of this file. `b, T, ϑ` first; then fixed regularity constants `δ, C₀`;
then for `ε, D > 0` a constant `C`; uniformly in `4 ≤ n ≤ TW`, models, pairs and splitting laws
there is an event `Ω` of every pair-law probability `≤ C W^{-D}` outside which, at every selected
bulk energy `E = λ_α` (`ϑ`-bulk `α`), with `K₀ = F(E) - E`, `A = K₀ + G_d`, `s = min(b, 1-2b)`,
`d = 2W`, `η = W^{-3/5}`, `R_η = (A - iη)⁻¹`, `m = m_E` (`pairDyson`) and the centre
`g(λ) = d⁻¹ Tr K₀Γ_E(λ)` (`windowCenter K₀ K₀`):
* (regularity) for `|λ| ≤ δ` the shift `λ + s m_E(λ)` lies in the
  compact set `{Im ≥ 1/C₀, |·| ≤ C₀}`; `g` is `C₀`-Lipschitz on `[-δ, δ]`; `|m_E(iη) - m_E(0)| ≤ C₀η`;
* (centre and certificate) `|g(0) + sE| ≤ C W^{-1+ε}` and
  `|m_E(0) - m_sc(E)| ≤ C W^{-1+ε}`, `m_sc(E) = conj(matchedA E)`;
* (averaged local law) `|Tr R_η - d m_E(iη)| ≤ C W^ε/η`;
* (Gaussian IBP and Poincaré on grids) `|Tr G_dR_η + sd m_E(iη)²| ≤ C W^{9/10+ε}`. -/
def SelectedResolventStatement : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
    ∃ δ C₀ : ℝ, 0 < δ ∧ 0 < C₀ ∧
      ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D →
        ∃ C : ℝ, ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
          ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
            IsPairSplitting p i model (splitS p) Pω →
              ∃ Ω : Set (SplitState p i × PairMatrix p i),
                (∀ α : Fin p.N, splitPairLaw p i α Pω Ω ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
                ∀ x ∉ Ω, ∀ α : Fin p.N, IsBulkRank p ϑ α →
                  let E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α
                  let K := schurK0 p i x.1 E
                  let s := splitS p
                  let η := (p.W : ℝ) ^ (-(3 / 5 : ℝ))
                  let Rη := (schurA p i x.1 x.2 E - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i))⁻¹
                  (∀ lam : ℝ, |lam| ≤ δ →
                    C₀⁻¹ ≤ ((lam : ℂ) + (s : ℂ) * pairDyson p i K s lam).im ∧
                      ‖(lam : ℂ) + (s : ℂ) * pairDyson p i K s lam‖ ≤ C₀) ∧
                  (∀ x ∈ Icc (-δ) δ, ∀ y ∈ Icc (-δ) δ,
                    |windowCenter p i K K s x - windowCenter p i K K s y| ≤ C₀ * |x - y|) ∧
                  ‖pairDyson p i K s ((η : ℂ) * Complex.I) - pairDyson p i K s 0‖ ≤ C₀ * η ∧
                  |windowCenter p i K K s 0 + s * E| ≤ C * (p.W : ℝ) ^ (-1 + ε) ∧
                  ‖pairDyson p i K s 0 - conj (matchedA E)‖ ≤ C * (p.W : ℝ) ^ (-1 + ε) ∧
                  ‖Rη.trace - ((2 * p.W : ℝ) : ℂ) * pairDyson p i K s ((η : ℂ) * Complex.I)‖ ≤
                    C * (p.W : ℝ) ^ ε / η ∧
                  ‖(x.2 * Rη).trace + (s : ℂ) * ((2 * p.W : ℝ) : ℂ) *
                      pairDyson p i K s ((η : ℂ) * Complex.I) ^ 2‖ ≤
                    C * (p.W : ℝ) ^ (9 / 10 + ε)

/-!
## Small facts
-/

theorem l2Norm_eq_one_of_dot {ι : Type} [Fintype ι] {v : ι → ℂ} (hv : star v ⬝ᵥ v = 1) :
    l2Norm v = 1 := by
  have h := congrArg Complex.re hv
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.conj_mul',
    Complex.one_re] at h
  unfold l2Norm
  rw [Real.sqrt_eq_one, ← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  norm_cast

theorem filter_poisson_le {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) {η : ℝ} (δ : ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j ≠ 0 ∧ |hA.eigenvalues j| ≤ δ),
        η ^ 2 / (hA.eigenvalues j ^ 2 + η ^ 2) ≤ spectralSum A (fun l => η ^ 2 / (l ^ 2 + η ^ 2)) := by
  unfold spectralSum
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_map_val]
  refine le_of_le_of_eq (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun j _ _ => by positivity) ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem schurK0_isHermitian {p : Parameters} {i : ZMod p.n} {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ) : (schurK0 p i ω E).IsHermitian := by
  have hF := physicalCoareaF_isHermitian hR ω.2.1 hV E
  have hE : ((E : ℂ) • (1 : PairMatrix p i)).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_one]; simp
  unfold schurK0
  exact hF.sub hE

theorem rpow_neg_six_ge {W δ' : ℝ} (hW : 0 < W) (hδ' : 0 < δ')
    (h : δ' < W ^ (-(3 / 5 : ℝ))) : 1 ≤ δ' ^ (-10 : ℝ) * W ^ (-(6 : ℝ)) := by
  have h1 : (W ^ (-(3 / 5 : ℝ))) ^ (-10 : ℝ) < δ' ^ (-10 : ℝ) :=
    Real.rpow_lt_rpow_of_neg hδ' h (by norm_num)
  rw [← Real.rpow_mul hW.le, show (-(3 / 5 : ℝ)) * (-10) = 6 by norm_num] at h1
  have h6 : 0 < W ^ (6 : ℝ) := Real.rpow_pos_of_pos hW _
  rw [Real.rpow_neg hW.le, ← div_eq_mul_inv, le_div_iff₀ h6, one_mul]
  exact h1.le

/-!
## The constants
-/

/-- The constant of `good_bound` (unsmoothing). -/
def goodConstU (C0u δ : ℝ) : ℝ := Classical.choose (good_bound C0u δ)

def c0uOf (CG CR C₀ C₁ : ℝ) : ℝ := max (max CG (CR + 2)) (max C₀ (C₁ / 2))

def a0Of (CG CLW C₀ : ℝ) : ℝ := 2 * (1 + CG) ^ 2 + CLW + 2 * (2 + 2 * C₀ ^ 4)

def kAOf (Cu A0 CR C0u C₀ : ℝ) : ℝ :=
  4 * Cu + 2 * CR + C0u * CR + 4 + 8 * C₀ + 12 * CR + 2 * Cu * A0 + 2 * CR

def kBOf (Cu A0 CR : ℝ) : ℝ := 2 * Cu * A0 + 2 * CR

/-!
## The good event
-/

/-- **The bound on the good event**: at a point of the pair-law support where
the local window (for the cutoff observable), the selected-energy inputs and the Gaussian norm
bound hold, `|Tr G'R - sE Tr R - (sd - 1)| ≤ K_A W^{98/100} + K_B W^{-102/100} ‖R‖²_HS`. -/
theorem good_case_bound {p : Parameters} {i : ZMod p.n} {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian) (hv : l2Norm θ.2.2 = 1)
    {G' : FrameMatrix p} (hG' : G'.IsHermitian)
    (hdetF : (frameM p i U θ.1 θ.2.1 θ.2.2 G').det ≠ 0)
    {W η ηL L s E : ℝ} {Gd K₀ A : PairMatrix p i}
    (hWd : W = p.W) (hηd : η = W ^ (-(3 / 5 : ℝ))) (hηL : ηL = W ^ (-1 + 2 / 5 : ℝ))
    (hLd : L = W ^ (1 / 4 : ℝ)) (hsd : s = splitS p) (hEd : E = θ.2.1)
    (hGdd : Gd = reconstructedGaussian p i U θ.1 E θ.2.2 G') (hK₀d : K₀ = schurK0 p i θ.1 E)
    (hAd : A = schurA p i θ.1 Gd E) (hEabs : |E| ≤ 2)
    {δL δR C₀ C₁ CG CLW CR : ℝ} (hδL : 0 < δL) (hδL1 : δL < 1) (hδR : 0 < δR) (hC₀ : 0 < C₀)
    (hCG : 0 < CG) (hCLW : 0 ≤ CLW) (hCR : 0 ≤ CR)
    (hl : η ≤ min (min δL δR) (1 / (C₀ + CR + 1))) (hGd : ‖Gd‖ ≤ CG)
    (hpois : spectralSum A (fun l => ηL ^ 2 / (l ^ 2 + ηL ^ 2)) ≤ C₁ * W * ηL)
    (hETH : ∀ lam : ℝ, |lam| ≤ δL → ∀ u : PairSite p i → ℂ, l2Norm u = 1 →
      A *ᵥ u = (lam : ℂ) • u →
      |(star u ⬝ᵥ (spectralFn (dilatedCutoff L) K₀ *ᵥ u)).re -
        windowCenter p i (spectralFn (dilatedCutoff L) K₀) K₀ s lam| ≤
        CLW * W ^ (-(1 / 2 : ℝ) + 1 / 100))
    (hreg : ∀ lam : ℝ, |lam| ≤ δR →
      C₀⁻¹ ≤ ((lam : ℂ) + (s : ℂ) * pairDyson p i K₀ s lam).im ∧
        ‖(lam : ℂ) + (s : ℂ) * pairDyson p i K₀ s lam‖ ≤ C₀)
    (hlip : ∀ x ∈ Icc (-δR) δR, ∀ y ∈ Icc (-δR) δR,
      |windowCenter p i K₀ K₀ s x - windowCenter p i K₀ K₀ s y| ≤ C₀ * |x - y|)
    (hmη : ‖pairDyson p i K₀ s ((η : ℂ) * Complex.I) - pairDyson p i K₀ s 0‖ ≤ C₀ * η)
    (hg0 : |windowCenter p i K₀ K₀ s 0 + s * E| ≤ CR * W ^ (-1 + 1 / 100 : ℝ))
    (hm0 : ‖pairDyson p i K₀ s 0 - conj (matchedA E)‖ ≤ CR * W ^ (-1 + 1 / 100 : ℝ))
    (hτ : ‖(A - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i))⁻¹.trace -
        ((2 * W : ℝ) : ℂ) * pairDyson p i K₀ s ((η : ℂ) * Complex.I)‖ ≤ CR * W ^ (1 / 100 : ℝ) / η)
    (hγ : ‖(Gd * (A - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i))⁻¹).trace + (s : ℂ) *
        ((2 * W : ℝ) : ℂ) * pairDyson p i K₀ s ((η : ℂ) * Complex.I) ^ 2‖ ≤
        CR * W ^ (9 / 10 + 1 / 100 : ℝ)) :
    |weightedTraceError s U θ G'| ≤
      kAOf (goodConstU (c0uOf CG CR C₀ C₁) (min δL δR)) (a0Of CG CLW C₀) CR (c0uOf CG CR C₀ C₁) C₀ *
          (W ^ (1 / 100 : ℝ)) ^ (98 : ℤ) +
        kBOf (goodConstU (c0uOf CG CR C₀ C₁) (min δL δR)) (a0Of CG CLW C₀) CR *
          (W ^ (1 / 100 : ℝ)) ^ (-102 : ℤ) * invHS U θ G' ^ 2 := by
  subst hWd hsd hEd hGdd hK₀d hAd
  set W : ℝ := (p.W : ℝ) with hWdef
  set s := splitS p with hsdef
  set E := θ.2.1 with hEdef
  set C0u := c0uOf CG CR C₀ C₁ with hC0u
  set δ := min δL δR with hδ
  set Cu := goodConstU C0u δ with hCudef
  have hCu0 : 0 ≤ Cu := (Classical.choose_spec (good_bound C0u δ)).1
  have hCu := (Classical.choose_spec (good_bound C0u δ)).2
  set A0 := a0Of CG CLW C₀ with hA0
  have hs0 := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (p.b_lt_half.le.trans (by norm_num))
  have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < W := by linarith
  set w : ℝ := W ^ (1 / 100 : ℝ) with hwdef
  have hw1 : 1 ≤ w := Real.one_le_rpow hW1 (by norm_num)
  have cv := fun (x : ℝ) (k : ℤ) (hx : x = k / 100) => rpow_hundredth hW0 x k hx
  have hWw : W = w ^ (100 : ℤ) := by rw [← cv 1 100 (by norm_num), Real.rpow_one]
  have hηw : η = w ^ (-60 : ℤ) := by rw [hηd]; exact cv _ (-60) (by norm_num)
  have hη0 : 0 < η := by rw [hηd]; exact Real.rpow_pos_of_pos hW0 _
  have hηL' : ηL = η := by rw [hηL, hηd]; norm_num
  have hL1 : 1 ≤ L := by rw [hLd]; exact Real.one_le_rpow hW1 (by norm_num)
  have hLw : L = w ^ (25 : ℤ) := by rw [hLd]; exact cv _ 25 (by norm_num)
  have hC0u0 : 0 ≤ C0u := hCG.le.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hδ0 : 0 < δ := lt_min hδL hδR
  set Gd := reconstructedGaussian p i U θ.1 E θ.2.2 G' with hGd'
  set K₀ := schurK0 p i θ.1 E with hK₀
  set A := schurA p i θ.1 Gd E with hAdef
  have hA : A.IsHermitian := schurA_rec_isHermitian U hR hV E θ.2.2 hG'
  have hK₀h : K₀.IsHermitian := schurK0_isHermitian hR hV E
  have hdetM : (outerM U θ G').det ≠ 0 := hdetF
  have hMP : IsMoorePenroseInverse A (embeddedInverse U θ G') := by
    rw [hAdef, schurA_rec_eq hU θ.1 E hv G']
    exact isMoorePenrose_frame (hU.2 θ.2.2 hv).1 hdetM
  have hcard := card_pairSite_real (p := p) (i := i)
  have hηδ : η ≤ δ := hl.trans (min_le_left _ _)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt hδL1
  set g₀ : ℝ → ℝ := fun lam => windowCenter p i K₀ K₀ s lam with hg₀
  -- the centre
  have hW99 : W ^ (-1 + 1 / 100 : ℝ) = w ^ (-99 : ℤ) := cv _ (-99) (by norm_num)
  have hw99 : w ^ (-99 : ℤ) ≤ 1 := by
    rw [show (1 : ℝ) = w ^ (0 : ℤ) by simp]; exact zpow_mono_one hw1 (by norm_num)
  set e₃ := CR * w ^ (-99 : ℤ) with he₃
  have hg0' : |g₀ 0 + s * E| ≤ e₃ := by rw [he₃, ← hW99]; exact hg0
  have hg00 : |g₀ 0| ≤ C0u := by
    have h1 : |s * E| ≤ 2 := by
      rw [abs_mul, abs_of_pos hs0]
      calc s * |E| ≤ 1 * 2 := mul_le_mul hs1 hEabs (abs_nonneg _) zero_le_one
        _ = 2 := one_mul 2
    have h2 : e₃ ≤ CR := by rw [he₃]; exact mul_le_of_le_one_right hCR hw99
    have h3 := abs_add_le (g₀ 0 + s * E) (-(s * E))
    rw [add_neg_cancel_right, abs_neg] at h3
    have h4 : CR + 2 ≤ C0u := (le_max_right _ _).trans (le_max_left _ _)
    linarith only [h1, h2, h3, h4, hg0']
  -- the ETH
  set a₀ := 2 / L * (1 + CG) ^ 2 + L * (CLW * W ^ (-(1 / 2 : ℝ) + 1 / 100)) +
    2 * s / L * (2 + 2 * C₀ ^ 4) with ha₀
  have hETH' : ∀ (lam : ℝ) (u : PairSite p i → ℂ), lam ≠ 0 → |lam| ≤ δ →
      A *ᵥ u = (lam : ℂ) • u → star u ⬝ᵥ u = 1 →
      ‖star u ⬝ᵥ (K₀ *ᵥ u) - ((g₀ lam : ℝ) : ℂ)‖ ≤ a₀ := by
    intro lam u _ hlam hAu hu
    obtain ⟨hzi, hzn⟩ := hreg lam (hlam.trans (min_le_right _ _))
    have hwin := hETH lam (hlam.trans (min_le_left _ _)) u (l2Norm_eq_one_of_dot hu) hAu
    exact eth_unbounded hK₀h rfl hGd hL1 hs0.le hC₀ hzi hzn (hlam.trans hδ1.le) hu hAu hwin
  have ha₀0 : 0 ≤ a₀ := by
    have : 0 ≤ W ^ (-(1 / 2 : ℝ) + 1 / 100) := (Real.rpow_pos_of_pos hW0 _).le
    have hL0 : 0 < L := by linarith
    positivity
  -- Poisson
  have hpois' : ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j ≠ 0 ∧ |hA.eigenvalues j| ≤ δ),
      η ^ 2 / (hA.eigenvalues j ^ 2 + η ^ 2) ≤ C0u * (Fintype.card (PairSite p i) : ℝ) * η := by
    refine (filter_poisson_le hA δ).trans ?_
    rw [hηL'] at hpois
    refine hpois.trans ?_
    rw [hcard]
    have : C₁ / 2 ≤ C0u := (le_max_right _ _).trans (le_max_right _ _)
    have hWη : 0 ≤ W * η := by positivity
    nlinarith only [this, hWη]
  -- smoothed inputs
  set a := pairDyson p i K₀ s ((η : ℂ) * Complex.I) with ha
  set σ := conj (matchedA E) with hσ
  set e₁ := CR * w ^ (61 : ℤ) with he₁
  set e₂ := CR * w ^ (91 : ℤ) with he₂
  set r := C₀ * η + e₃ with hr
  have hτ' : ‖(A - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i))⁻¹.trace -
      ((Fintype.card (PairSite p i) : ℝ) : ℂ) * a‖ ≤ e₁ := by
    rw [hcard]; refine hτ.trans (le_of_eq ?_)
    have : w / w ^ (-60 : ℤ) = w ^ (61 : ℤ) := by
      rw [div_eq_mul_inv, ← _root_.zpow_neg, neg_neg, ← zpow_one_add₀ (by positivity)]; norm_num
    rw [hηw, mul_div_assoc, this]
  have hγ' : ‖(Gd * (A - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i))⁻¹).trace +
      (s : ℂ) * ((Fintype.card (PairSite p i) : ℝ) : ℂ) * a ^ 2‖ ≤ e₂ := by
    rw [hcard]; refine hγ.trans (le_of_eq ?_)
    rw [show W ^ (9 / 10 + 1 / 100 : ℝ) = w ^ (91 : ℤ) from cv _ 91 (by norm_num)]
  have har : ‖a - σ‖ ≤ r := by
    have h1 : ‖pairDyson p i K₀ s 0 - σ‖ ≤ e₃ := by rw [he₃, ← hW99]; exact hm0
    calc ‖a - σ‖ ≤ ‖a - pairDyson p i K₀ s 0‖ + ‖pairDyson p i K₀ s 0 - σ‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C₀ * η + e₃ := add_le_add hmη h1
  have hr1 : r ≤ 1 := by
    have hη1 : η ≤ 1 / (C₀ + CR + 1) := hl.trans (min_le_right _ _)
    have he₃η : e₃ ≤ CR * η := by
      rw [he₃, hηw]
      exact mul_le_mul_of_nonneg_left (zpow_mono_one hw1 (by norm_num)) hCR
    have h2 : (C₀ + CR + 1) * η ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hη1; linarith only [hη1]
    rw [hr]
    nlinarith only [he₃η, h2, hη0]
  obtain ⟨hσ1, hσE⟩ := matchedA_norm hEabs
  have hlip' : ∀ x ∈ Icc (-δ) δ, ∀ y ∈ Icc (-δ) δ, |g₀ x - g₀ y| ≤ C0u * |x - y| := by
    intro x hx y hy
    have hsub : Icc (-δ) δ ⊆ Icc (-δR) δR :=
      Icc_subset_Icc (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
    refine (hlip x (hsub hx) y (hsub hy)).trans ?_
    exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (abs_nonneg _)
  have hGd' : ‖Gd‖ ≤ C0u := hGd.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hmain := hCu (PairSite p i) A K₀ Gd (embeddedInverse U θ G') hA g₀ a₀ η s E e₁ e₂ e₃ r a σ
    rfl hK₀h hMP hη0 hηδ hδ1 hGd' hg00 hlip' ha₀0 hETH' hpois' hs0.le hs1 hτ' hγ' har hr1
    hσ1 hσE hg0'
  rw [hcard, hsNorm_embeddedInverse hU hv G'] at hmain
  have hX := weightedTraceError_eq hU s hv hdetM
  rw [← hX] at hmain
  -- exponents
  have ha₀w : a₀ ≤ A0 * w ^ (-24 : ℤ) := by
    have hL' : 2 / L ≤ 2 * w ^ (-24 : ℤ) := by
      rw [hLw, div_eq_mul_inv, ← _root_.zpow_neg]
      exact mul_le_mul_of_nonneg_left (zpow_mono_one hw1 (by norm_num)) (by norm_num)
    have hLe : L * (CLW * W ^ (-(1 / 2 : ℝ) + 1 / 100)) = CLW * w ^ (-24 : ℤ) := by
      rw [cv (-(1 / 2 : ℝ) + 1 / 100) (-49) (by norm_num), hLw, mul_left_comm,
        zpow_mul_zpow hw1]
      norm_num
    have hsL : 2 * s / L ≤ 2 * w ^ (-24 : ℤ) := by
      have hL0 : 0 < L := by linarith
      calc 2 * s / L ≤ 2 * 1 / L := div_le_div_of_nonneg_right (by linarith only [hs1]) hL0.le
        _ = 2 / L := by ring
        _ ≤ _ := hL'
    have h1 : 2 / L * (1 + CG) ^ 2 ≤ 2 * w ^ (-24 : ℤ) * (1 + CG) ^ 2 :=
      mul_le_mul_of_nonneg_right hL' (sq_nonneg _)
    have h3 : 2 * s / L * (2 + 2 * C₀ ^ 4) ≤ 2 * w ^ (-24 : ℤ) * (2 + 2 * C₀ ^ 4) :=
      mul_le_mul_of_nonneg_right hsL (by positivity)
    rw [ha₀, hLe, hA0]
    unfold a0Of
    linarith only [h1, h3]
  have hs₁ : Real.sqrt (2 * W * η) = Real.sqrt 2 * w ^ (20 : ℤ) := by
    rw [hWw, hηw, mul_assoc, zpow_mul_zpow hw1, Real.sqrt_mul (by norm_num),
      show (100 : ℤ) + -60 = 20 * 2 by norm_num, _root_.zpow_mul]
    rw [show ((w ^ (20 : ℤ)) ^ (2 : ℤ)) = (w ^ (20 : ℤ)) ^ (2 : ℕ) by norm_cast,
      Real.sqrt_sq (by positivity)]
  have hs₂ : Real.sqrt (2 * W) = Real.sqrt 2 * w ^ (50 : ℤ) := by
    rw [Real.sqrt_mul (by norm_num), hWw, show (100 : ℤ) = 50 * 2 by norm_num, _root_.zpow_mul]
    rw [show ((w ^ (50 : ℤ)) ^ (2 : ℤ)) = (w ^ (50 : ℤ)) ^ (2 : ℕ) by norm_cast,
      Real.sqrt_sq (by positivity)]
  have hgood := good_arith (W := W) (η := η) (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (r := r)
    (a₀ := a₀) (ρ := invHS U θ G') (Cu := Cu) (A0 := A0) (CR := CR) (C0u := C0u) (C₀ := C₀)
    hw1 hWw hηw hs₁ hs₂ rfl rfl rfl rfl ha₀w ha₀0 (Real.sqrt_nonneg _) hCu0 hCR hC0u0 hC₀.le
  unfold kAOf kBOf
  exact hmain.trans hgood

/-!
## The theorem
-/

set_option maxHeartbeats 1000000 in

/-- :
`E♯ 1{E ∈ I}|Tr G_dR − sE Tr R − (sd−1)| ≤
C W^{49/50}`, under the `CoareaContract`, and the named
selected-energy inputs `SelectedResolventStatement`.
-/
theorem physicalWeightedTrace_holds (hC : CoareaContract) (hLW : PhysicalLocalWindowStatement)
    (hSR : SelectedResolventStatement) : PhysicalWeightedTraceStatement := by
  intro b T ϑ κ hϑ hκ
  obtain ⟨δL, cL, C₁, k, hδL, hδL1, -, hC₁, hLW'⟩ := hLW b T ϑ hϑ
  obtain ⟨Kf, -, hKf⟩ := isSpectralTest_dilatedCutoff k
  obtain ⟨CLW, hCLW⟩ := hLW' (2 / 5) (by norm_num) (by norm_num) (1 / 100) (by norm_num) 6
    (by norm_num) Kf
  obtain ⟨δR, C₀, hδR, hC₀, hSR'⟩ := hSR b T ϑ hϑ
  obtain ⟨CR, hCR⟩ := hSR' (1 / 100) (by norm_num) 6 (by norm_num)
  obtain ⟨CG, cG, hCG, hcG, htail⟩ := gueNormTail_holds
  obtain ⟨Ccol, hCcol⟩ := physicalColumn_holds hC b 2 le_rfl (by norm_num)
  set CLW' := max CLW 0 with hCLW'
  set CR' := max CR 0 with hCR'
  have hCLW0 : 0 ≤ CLW' := le_max_right _ _
  have hCR0 : 0 ≤ CR' := le_max_right _ _
  set C0u := c0uOf CG CR' C₀ C₁ with hC0u
  have hC0u0 : 0 ≤ C0u := hCG.le.trans ((le_max_left _ _).trans (le_max_left _ _))
  set Cu := goodConstU C0u (min δL δR) with hCudef
  have hCu0 : 0 ≤ Cu := (Classical.choose_spec (good_bound C0u (min δL δR))).1
  set A0 := a0Of CG CLW' C₀ with hA0
  have hA00 : 0 ≤ A0 := by rw [hA0]; unfold a0Of; positivity
  set KA := kAOf Cu A0 CR' C0u C₀ with hKA
  set KB := kBOf Cu A0 CR' with hKB
  have hKA0 : 0 ≤ KA := by rw [hKA]; unfold kAOf; positivity
  have hKB0 : 0 ≤ KB := by rw [hKB]; unfold kBOf; positivity
  set Mg := CG ^ (4 : ℝ) + T / (2 * cG) * gueMomentConst (2 * 4) ^ (1 / 2 : ℝ) with hMg
  set KG := T / 2 * (5040 / (2 * cG) ^ 7) with hKG
  set δ' := min (min δL δR) (1 / (C₀ + CR' + 1)) with hδ'
  have hδ'0 : 0 < δ' := lt_min (lt_min hδL hδR) (by positivity)
  set Cs := δ' ^ (-10 : ℝ) with hCs
  have hCs0 : 0 ≤ Cs := Real.rpow_nonneg hδ'0.le _
  set Cb := CLW' + CR' + KG + Cs with hCb
  refine ⟨KA + (KB + 1) * max Ccol 0 + Mg + 8 * Cb, ?_⟩
  intro p hb hn model α hα i Pω hPω U hU
  set s := splitS p with hsdef
  have hs0 := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (p.b_lt_half.le.trans (by norm_num))
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hT0 : 0 ≤ T := by
    have h0 : (0 : ℝ) < p.n := by exact_mod_cast (show 0 < p.n by have := p.n_ge_four; omega)
    by_contra h
    have : T * (p.W : ℝ) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) hW0
    linarith
  have hKG0 : 0 ≤ KG := by positivity
  have hMg0 : 0 ≤ Mg := by
    have := Real.rpow_nonneg (gueMomentConst_nonneg (show (0 : ℝ) < 2 * 4 by norm_num)) (1 / 2 : ℝ)
    have := Real.rpow_nonneg hCG.le (4 : ℝ)
    positivity
  have hCb0 : 0 ≤ Cb := by positivity
  set W : ℝ := (p.W : ℝ) with hWdef
  set w : ℝ := W ^ (1 / 100 : ℝ) with hwdef
  have hw1 : 1 ≤ w := Real.one_le_rpow hW1 (by norm_num)
  have cv := fun (x : ℝ) (k : ℤ) (hx : x = k / 100) => rpow_hundredth hW0 x k hx
  have hWw : W = w ^ (100 : ℤ) := by rw [← cv 1 100 (by norm_num), Real.rpow_one]
  set η : ℝ := W ^ (-(3 / 5 : ℝ)) with hηdef
  set L : ℝ := W ^ (1 / 4 : ℝ) with hLdef
  have hL1 : 1 ≤ L := Real.one_le_rpow hW1 (by norm_num)
  -- the events
  obtain ⟨ΩL, -, hΩLα, hΩL⟩ := hCLW p hb hn model i Pω hPω
    (fun om E => spectralFn (dilatedCutoff L) (schurK0 p i om E))
    (isWindowObservable_cutoff (hKf L hL1))
  obtain ⟨ΩR, hΩRα, hΩR⟩ := hCR p hb hn model i Pω hPω
  set N : Set (SplitState p i × PairMatrix p i) := {x | CG < ‖x.2‖} with hN
  set μ := splitPairLaw p i α Pω with hμ
  set Ωt := ΩL ∪ ΩR ∪ N with hΩt
  set Ω' := toMeasurable μ Ωt with hΩ'
  have hΩ'm : MeasurableSet Ω' := measurableSet_toMeasurable _ _
  have hW6 : W ^ (-(6 : ℝ)) = w ^ (-600 : ℤ) := cv _ (-600) (by norm_num)
  have hW6p : 0 ≤ W ^ (-(6 : ℝ)) := (Real.rpow_pos_of_pos hW0 _).le
  have hμΩt : μ Ωt ≤ ENNReal.ofReal ((CLW' + CR' + KG) * W ^ (-(6 : ℝ))) := by
    have h1 : μ ΩL ≤ ENNReal.ofReal (CLW' * W ^ (-(6 : ℝ))) :=
      (hΩLα α).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hW6p))
    have h2 : μ ΩR ≤ ENNReal.ofReal (CR' * W ^ (-(6 : ℝ))) :=
      (hΩRα α).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hW6p))
    have h3 : μ N ≤ ENNReal.ofReal (KG * W ^ (-(6 : ℝ))) :=
      (splitPairLaw_gauss_le hPω α hCG htail).trans (ENNReal.ofReal_le_ofReal
        (half_exp_le_rpow (Nat.cast_nonneg _) hW1 hcG hn))
    calc μ Ωt ≤ μ (ΩL ∪ ΩR) + μ N := measure_union_le _ _
      _ ≤ μ ΩL + μ ΩR + μ N := by gcongr; exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (CLW' * W ^ (-(6 : ℝ))) + ENNReal.ofReal (CR' * W ^ (-(6 : ℝ))) +
          ENNReal.ofReal (KG * W ^ (-(6 : ℝ))) := by gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  -- the exceptional indicator
  set large : Prop := η ≤ δ' with hlarge
  set bfun : OuterData p i → FrameMatrix p → ℝ≥0∞ := fun θ G' =>
    if large then Ω'.indicator 1 (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') else 1
    with hbfun
  have hbm : Measurable fun z : OuterData p i × FrameMatrix p => bfun z.1 z.2 := by
    simp only [hbfun]
    by_cases hl : large
    · simp only [hl, ↓reduceIte]
      exact (measurable_one.indicator hΩ'm).comp (measurable_fst.fst.prodMk (measurable_recG hU.1))
    · simp only [hl, ↓reduceIte]
      exact measurable_const
  have hbE : pairExpect α s U Pω bfun ≤ ENNReal.ofReal (Cb * W ^ (-(6 : ℝ))) := by
    by_cases hl : large
    · have : bfun = fun θ G' =>
          Ω'.indicator 1 (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') := by
        simp only [hbfun, hl, ↓reduceIte]
      rw [this, pairExpect_hull_eq hC hPω hU α Ωt]
      refine hμΩt.trans (ENNReal.ofReal_le_ofReal ?_)
      have := mul_nonneg hCs0 hW6p
      rw [hCb]; nlinarith only [this]
    · have : bfun = fun _ _ => 1 := by simp only [hbfun, hl, ↓reduceIte]
      rw [this]
      refine (pairExpect_one_le hC hPω hU α).trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := rpow_neg_six_ge hW0 hδ'0 (lt_of_not_ge hl)
      have h2 : 0 ≤ (CLW' + CR' + KG) * W ^ (-(6 : ℝ)) := by positivity
      rw [hCb, add_mul]; linarith only [h1, h2]
  -- the pointwise bound
  set c₀ : ℝ := KA * w ^ (98 : ℤ) with hc₀
  set c₁ : ℝ := (KB + 1) * w ^ (-102 : ℤ) with hc₁
  set c₃ : ℝ := 8 * w ^ (602 : ℤ) with hc₃
  have hc10 : 0 ≤ c₁ := by positivity
  have hc00 : 0 ≤ c₀ := by positivity
  have hc30 : 0 ≤ c₃ := by positivity
  have hs₂ : Real.sqrt (2 * W) = Real.sqrt 2 * w ^ (50 : ℤ) := by
    rw [Real.sqrt_mul (by norm_num), hWw, show (100 : ℤ) = 50 * 2 by norm_num, _root_.zpow_mul]
    rw [show ((w ^ (50 : ℤ)) ^ (2 : ℤ)) = (w ^ (50 : ℤ)) ^ (2 : ℕ) by norm_cast,
      Real.sqrt_sq (by positivity)]
  have hpt : pairExpect α s U Pω (fun θ G' => (bulkInterval κ).indicator 1 θ.2.1 *
        ENNReal.ofReal |weightedTraceError s U θ G'|) ≤
      pairExpect α s U Pω (fun θ G' =>
        (ENNReal.ofReal (c₁ * invHS U θ G' ^ (2 : ℝ)) + ENNReal.ofReal c₀) +
          ENNReal.ofReal (‖reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'‖ ^ (4 : ℝ)) +
          ENNReal.ofReal c₃ * bfun θ G') := by
    refine pairExpect_mono_ae hPω α U fun θ hR hV hv hE => ?_
    filter_upwards [ae_isHermitian_gue (pairTime p s)] with G' hG' hsw
    by_cases hEI : θ.2.1 ∈ bulkInterval κ
    swap
    · rw [Set.indicator_of_notMem hEI, zero_mul]; exact zero_le
    rw [Set.indicator_of_mem hEI, Pi.one_apply, one_mul]
    have hEabs : |θ.2.1| ≤ 2 := by
      obtain ⟨h1, h2⟩ := hEI
      rw [abs_le]; constructor
      · linarith only [h1, hκ]
      · linarith only [h2, hκ]
    have hdetF : (frameM p i U θ.1 θ.2.1 θ.2.2 G').det ≠ 0 := by
      intro h0; apply hsw; unfold sectorWeight outerM; rw [h0]; simp
    have hsec : negativeCount (frameM p i U θ.1 θ.2.1 θ.2.2 G') +
        negativeCount (θ.1.1 - (θ.2.1 : ℂ) • 1) = α.val := by
      by_contra h; apply hsw; unfold sectorWeight outerM; split_ifs; simp
    set ρ := invHS U θ G' with hρ
    set g := ‖reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'‖ with hg
    have hρ2 : ρ ^ (2 : ℝ) = ρ ^ 2 := Real.rpow_two ρ
    have hg4 : g ^ (4 : ℝ) = g ^ 4 := by norm_cast
    have hsum : ∀ (bb : ℝ≥0∞), (bb = 1 ∨ bb = 0) →
        ENNReal.ofReal (c₁ * ρ ^ 2 + c₀ + g ^ 4 + c₃ * bb.toReal) ≤
          (ENNReal.ofReal (c₁ * ρ ^ (2 : ℝ)) + ENNReal.ofReal c₀) + ENNReal.ofReal (g ^ (4 : ℝ)) +
            ENNReal.ofReal c₃ * bb := by
      intro bb hbb
      rw [hρ2, hg4, ← ENNReal.ofReal_add (by positivity) hc00,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      rcases hbb with h | h
      · rw [h, ENNReal.toReal_one, mul_one, mul_one, ← ENNReal.ofReal_add (by positivity) hc30]
      · rw [h, ENNReal.toReal_zero, mul_zero, mul_zero, add_zero, add_zero]
    by_cases hgood : large ∧ (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') ∉ Ω'
    swap
    · -- exceptional: `bfun = 1`, trivial bound
      have hb1 : bfun θ G' = 1 := by
        simp only [hbfun]
        by_cases hl : large
        · simp only [hl, ↓reduceIte]
          have : (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') ∈ Ω' := by
            by_contra h; exact hgood ⟨hl, h⟩
          rw [Set.indicator_of_mem this]; rfl
        · simp only [hl, ↓reduceIte]
      rw [hb1]
      have htriv := weightedTraceError_le_trivial hU hs0.le hv hEabs G'
      have hbad := bad_arith (g := g) (ρ := ρ) hw1 hWw hs₂ hs0.le hs1
      have hbadb : |weightedTraceError s U θ G'| ≤ c₁ * ρ ^ 2 + c₀ + g ^ 4 + c₃ * 1 := by
        have h1 : w ^ (-102 : ℤ) * ρ ^ 2 ≤ c₁ * ρ ^ 2 := by
          rw [hc₁]; refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have : 0 < w ^ (-102 : ℤ) := by positivity
          nlinarith only [this, hKB0]
        rw [hc₃]
        linarith only [htriv, hbad, h1, hc00]
      refine (ENNReal.ofReal_le_ofReal hbadb).trans ?_
      have := hsum 1 (Or.inl rfl)
      rwa [ENNReal.toReal_one] at this
    -- good event
    obtain ⟨hl, hxΩ⟩ := hgood
    have hb0 : bfun θ G' = 0 := by
      simp only [hbfun, hl, ↓reduceIte, Set.indicator_of_notMem hxΩ]
    rw [hb0]
    have hxt : (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') ∉ Ωt :=
      fun h => hxΩ (subset_toMeasurable _ _ h)
    have hxL := fun h => hxt (Or.inl (Or.inl h))
    have hxR := fun h => hxt (Or.inl (Or.inr h))
    have hxN : g ≤ CG := by
      have : (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') ∉ N :=
        fun h => hxt (Or.inr h)
      simpa [hN] using this
    have hrank := hC.reconstructed_rank p α i U hU θ.1 θ.2.1 θ.2.2 G'
      (assemble_reconstructedGaussian_isHermitian p i U hR hV θ.2.1 θ.2.2 hG') hv hE hdetF hsec
    have hEq : physicalOrderedEigenvalue p
        (assemble p i θ.1 (reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G')) α = θ.2.1 := hrank.1
    have hLWx := hΩL _ hxL α hα
    have hSRx := hΩR _ hxR α hα
    dsimp only at hLWx hSRx
    rw [hEq] at hLWx hSRx
    obtain ⟨⟨-, hpois⟩, hETH⟩ := hLWx
    obtain ⟨hreg, hlip, hmη, hg0, hm0, hτ, hγ⟩ := hSRx
    have hgc := good_case_bound hU hR hV hv hG' hdetF rfl rfl rfl rfl rfl rfl rfl rfl rfl hEabs
      hδL hδL1 hδR hC₀ hCG hCLW0 hCR0 hl hxN hpois
      (fun lam hlam u hu hAu => (hETH lam hlam u hu hAu).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hW0 _).le))
      hreg hlip hmη
      (hg0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hW0 _).le))
      (hm0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hW0 _).le))
      (hτ.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_pos_of_pos hW0 _).le) (Real.rpow_pos_of_pos hW0 _).le))
      (hγ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hW0 _).le))
    have hfin : |weightedTraceError s U θ G'| ≤ c₁ * ρ ^ 2 + c₀ + g ^ 4 + c₃ * 0 := by
      have hc : KB * w ^ (-102 : ℤ) * ρ ^ 2 ≤ (KB + 1) * w ^ (-102 : ℤ) * ρ ^ 2 := by
        have : 0 ≤ w ^ (-102 : ℤ) * ρ ^ 2 := by positivity
        nlinarith only [this]
      have hg4' : 0 ≤ g ^ 4 := by positivity
      rw [hc₁, hc₀, mul_zero, add_zero]
      linarith only [hgc, hc, hg4']
    refine (ENNReal.ofReal_le_ofReal hfin).trans ?_
    have := hsum 0 (Or.inr rfl)
    rwa [ENNReal.toReal_zero] at this
  -- integrate
  have hcol : pairExpect α s U Pω (fun θ G' => ENNReal.ofReal (invHS U θ G' ^ (2 : ℝ))) ≤
      ENNReal.ofReal (max Ccol 0 * W ^ (2 : ℝ)) := by
    refine ((hCcol p hb model α i Pω hPω U hU).2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hW0 _).le
  have hgm : pairExpect α s U Pω (fun θ G' =>
      ENNReal.ofReal (‖reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'‖ ^ (4 : ℝ))) ≤
      ENNReal.ofReal Mg :=
    (pairExpect_normPow_le hC hPω hU α hn hCG hcG htail (q := 4) (by norm_num)).trans
      (le_of_eq (by rw [hMg]))
  have hGm : Measurable fun z : OuterData p i × FrameMatrix p =>
      ENNReal.ofReal (‖reconstructedGaussian p i U z.1.1 z.1.2.1 z.1.2.2 z.2‖ ^ (4 : ℝ)) :=
    ((continuous_norm.measurable.comp (measurable_recG hU.1)).pow_const _).ennreal_ofReal
  have hc3m : Measurable fun z : OuterData p i × FrameMatrix p =>
      ENNReal.ofReal c₃ * bfun z.1 z.2 := hbm.const_mul _
  have hsplit := pairExpect_add_le_of_measurable α s hU.1 Pω
    (fun θ G' => (ENNReal.ofReal (c₁ * invHS U θ G' ^ (2 : ℝ)) + ENNReal.ofReal c₀) +
      ENNReal.ofReal (‖reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'‖ ^ (4 : ℝ)))
    (fun θ G' => ENNReal.ofReal c₃ * bfun θ G') hc3m
  have hsplit2 := pairExpect_add_le_of_measurable α s hU.1 Pω
    (fun θ G' => ENNReal.ofReal (c₁ * invHS U θ G' ^ (2 : ℝ)) + ENNReal.ofReal c₀)
    (fun θ G' => ENNReal.ofReal (‖reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'‖ ^ (4 : ℝ))) hGm
  have hsplit3 := pairExpect_add_le_of_measurable α s hU.1 Pω
    (fun θ G' => ENNReal.ofReal (c₁ * invHS U θ G' ^ (2 : ℝ)))
    (fun _ _ => ENNReal.ofReal c₀) measurable_const
  have hρc : pairExpect α s U Pω (fun θ G' => ENNReal.ofReal (c₁ * invHS U θ G' ^ (2 : ℝ))) ≤
      ENNReal.ofReal c₁ * ENNReal.ofReal (max Ccol 0 * W ^ (2 : ℝ)) := by
    have e : (fun θ G' => ENNReal.ofReal (c₁ * invHS U θ G' ^ (2 : ℝ))) =
        fun θ G' => ENNReal.ofReal c₁ * ENNReal.ofReal (invHS U θ G' ^ (2 : ℝ)) := by
      funext θ G'; rw [ENNReal.ofReal_mul hc10]
    rw [e, pairExpect_const_mul α s U Pω ENNReal.ofReal_ne_top]
    exact mul_le_mul_right hcol _
  have hc0c : pairExpect α s U Pω (fun _ _ => ENNReal.ofReal c₀) ≤ ENNReal.ofReal c₀ := by
    have := pairExpect_const_mul α s U Pω (ENNReal.ofReal_ne_top (r := c₀)) (fun _ _ => 1)
    simp only [mul_one] at this
    rw [this]
    calc ENNReal.ofReal c₀ * pairExpect α s U Pω (fun _ _ => 1) ≤ ENNReal.ofReal c₀ * 1 :=
          mul_le_mul_right (pairExpect_one_le hC hPω hU α) _
      _ = _ := mul_one _
  have hc3c : pairExpect α s U Pω (fun θ G' => ENNReal.ofReal c₃ * bfun θ G') ≤
      ENNReal.ofReal c₃ * ENNReal.ofReal (Cb * W ^ (-(6 : ℝ))) := by
    rw [pairExpect_const_mul α s U Pω ENNReal.ofReal_ne_top]
    exact mul_le_mul_right hbE _
  have hW2p : 0 ≤ W ^ (2 : ℝ) := (Real.rpow_pos_of_pos hW0 _).le
  have htot : pairExpect α s U Pω (fun θ G' => (bulkInterval κ).indicator 1 θ.2.1 *
        ENNReal.ofReal |weightedTraceError s U θ G'|) ≤
      ENNReal.ofReal (c₁ * (max Ccol 0 * W ^ (2 : ℝ)) + c₀ + Mg + c₃ * (Cb * W ^ (-(6 : ℝ)))) := by
    refine hpt.trans (hsplit.trans ?_)
    refine (add_le_add (hsplit2.trans (add_le_add (hsplit3.trans (add_le_add hρc hc0c)) hgm))
      hc3c).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hc10, ← ENNReal.ofReal_mul hc30,
      ← ENNReal.ofReal_add (by positivity) hc00,
      ← ENNReal.ofReal_add (by positivity) hMg0, ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
  refine htot.trans (ENNReal.ofReal_le_ofReal ?_)
  have hW2 : W ^ (2 : ℝ) = w ^ (200 : ℤ) := cv _ 200 (by norm_num)
  have hW98 : W ^ (49 / 50 : ℝ) = w ^ (98 : ℤ) := cv _ 98 (by norm_num)
  rw [hW2, hW6, hW98, hc₁, hc₀, hc₃]
  have e1 : (KB + 1) * w ^ (-102 : ℤ) * (max Ccol 0 * w ^ (200 : ℤ)) =
      (KB + 1) * max Ccol 0 * w ^ (98 : ℤ) := by
    rw [show (KB + 1) * w ^ (-102 : ℤ) * (max Ccol 0 * w ^ (200 : ℤ)) =
      (KB + 1) * max Ccol 0 * (w ^ (-102 : ℤ) * w ^ (200 : ℤ)) by ring, zpow_mul_zpow hw1]
    norm_num
  have e2 : 8 * w ^ (602 : ℤ) * (Cb * w ^ (-600 : ℤ)) = 8 * Cb * w ^ (2 : ℤ) := by
    rw [show 8 * w ^ (602 : ℤ) * (Cb * w ^ (-600 : ℤ)) = 8 * Cb * (w ^ (602 : ℤ) *
      w ^ (-600 : ℤ)) by ring, zpow_mul_zpow hw1]
    norm_num
  rw [e1, e2]
  have h98 : (1 : ℝ) ≤ w ^ (98 : ℤ) := by
    rw [show (1 : ℝ) = w ^ (0 : ℤ) by simp]; exact zpow_mono_one hw1 (by norm_num)
  have h2 : w ^ (2 : ℤ) ≤ w ^ (98 : ℤ) := zpow_mono_one hw1 (by norm_num)
  have h3 := mul_le_mul_of_nonneg_left h98 hMg0
  have h4 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 8 * Cb by positivity)
  nlinarith only [h3, h4]

end BlockBand.DeterminantScore.WeightedTrace
