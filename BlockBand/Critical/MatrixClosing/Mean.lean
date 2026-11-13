module

public import BlockBand.Critical.MatrixClosing.Mean.Estimate
public import BlockBand.Critical.MatrixClosing.Boundary
public import BlockBand.Critical.BoundaryMean.Main

/-!
# Matrix closing: the mean clause `CollarMeanClause`

* **`collarMeanClause_of_inputs : FreshPalmContract → PointDensityContract →
  CommonPortMeanContract → TraceMatrixContract → PSSS.SourceContract → CollarMeanClause`**
  (`E Im F_{W_n}(iY) → I_r` entrywise along every `OldSequence`, every `Y > 0`).
* `tendsto_collarMean_quad`: the same for one quadratic form `Re v*Im F(iY)v → ‖v‖²`, with
  eventual integrability.
* `matrixClosing_of_poles_inputs : CollarPolesClause → (inputs) → MatrixClosingStatement`. Since
  `CollarPolesClause` is false at frame rank `r = 0`, this implication is valid but vacuous; the
  `r ≥ 1` reduction (`Poles.CollarPolesAt`, `Poles.matrixClosing_of_clauses_pos`) uses
  `collarMeanClause_of_inputs` unchanged, and its end-to-end form is
  `Poles.matrixClosing_of_relativeVectors`.

Proof (the `Mean` modules). (1) `Form`: `Re v*Im F_W(iY)v = (π/η)Σ_ℓ P_ν(λ_ℓ(Q))|(T*K*Jv)*u_ℓ|²`,
`ν = Y/(Wρ(e))`. (2) `Spectral`: its collar expectation is `∫P_ν(s)ρ(s)ds`,
`ρ(s) = E_{A,B}(T*K*q)*Σ_F(s)(T*K*q)`, `q = Jv` (eigenpair kernel identity in the fresh `G`).
(3) `Shift`, `Window`: `ρ(s)` is the conditional density at `(e + s, X - s)`, so
`Collar.Density.lintegral_condCollarDensity_two_sided` gives `ρ(s) = (η/π)‖v‖² ±
(C(d(X) + ε_W) + B|s|)‖v‖²` for `|s| ≤ s₀` (the shifted weighted density). (4) `Tail`:
`∫P₁ρ ≤ C₁‖v‖²` (the distant collar bound: `(Q - i)⁻¹(F - ca)H = I + (Q - i)⁻¹(i - ca - G)H`,
`E‖L‖² ≤ C` from `CommonPortMeanContract.moments`, `E_G‖Gz‖² = c‖z‖²`). (5) `Limit`, `Estimate`:
`|E - ‖v‖²| ≤ (π/η)‖v‖²(C(d + ε_W) + Bσ + ν(1+σ⁻²)C₂)` for all `σ ≤ s₀`; `W → ∞` then `σ ↓ 0`;
polarization gives the matrix entries.

Hypotheses used: `CoareaPalm.FreshPalmContract`, `Critical.PointDensityContract`,
`Layers.TraceMatrixContract`, `PSSS.SourceContract` (only through
`lintegral_condCollarDensity_two_sided`), `Critical.CommonPortMeanContract` (there, and `.moments`
with `p = 2` for the distant bound). `ExactBoundaryMeanContract` is not used by the clause (only by
the corollary).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Mean

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Critical.Herglotz
open CoareaNative.BlockBand (matrixImaginaryPart matrixImaginaryPart_isHermitian)
open scoped ENNReal NNReal ComplexOrder

theorem star_dotProduct_self_eq' {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum,
    Complex.ofReal_pow]

/-- A uniform lower bound for the semicircle density on the bulk (as `semicircleDensity_ge`). -/
theorem semicircleDensity_ge' {κ e : ℝ} (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    0 < Real.sqrt (4 - (2 - κ) ^ 2) / (2 * Real.pi) ∧
      Real.sqrt (4 - (2 - κ) ^ 2) / (2 * Real.pi) ≤ Parameters.semicircleDensity e := by
  have hκ2 : κ ≤ 2 := by linarith [he.1, he.2]
  have hpos : 0 < 4 - (2 - κ) ^ 2 := by nlinarith
  refine ⟨div_pos (Real.sqrt_pos.2 hpos) (by positivity), ?_⟩
  unfold Parameters.semicircleDensity
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt
    (by linarith [BlockBand.Layers.sq_le_of_mem_bulkInterval he])) (by positivity)

/-- **Hypothesis 2 along an old sequence, one quadratic form.** For every `Y > 0` and `v`,
`Re v*Im F_{W_n}(iY)v` is eventually integrable and `E Re v*Im F_{W_n}(iY)v → ‖v‖²`. -/
theorem tendsto_collarMean_quad (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hCM : CommonPortMeanContract) (hTM : BlockBand.Internal.Contracts.Layers.TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) {r : ℕ} (S : OldSequence b κ r) {Y : ℝ} (hY : 0 < Y) (v : Fin r → ℂ) :
    (∀ᶠ N in atTop, Integrable (fun ω => (star v ⬝ᵥ (matrixImaginaryPart
        ((S.collarFns N ω).eval ((Y : ℂ) * Complex.I)) *ᵥ v)).re) (collarLaw (S.W N) b)) ∧
      Tendsto (fun N => ∫ ω, (star v ⬝ᵥ (matrixImaginaryPart
        ((S.collarFns N ω).eval ((Y : ℂ) * Complex.I)) *ᵥ v)).re ∂collarLaw (S.W N) b)
        atTop (𝓝 (∑ i, ‖v i‖ ^ 2)) := by
  obtain ⟨d₁, C, B, s₀, C₂, ε, W₀, hd₁, hC, hB, hs₀, hC₂, hε, hε0, hmain⟩ :=
    collarMean_estimate hP hPD hCM hTM source hb0 hb hκ
  set ηmin := (1 - b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2
  set ρmin := Real.sqrt (4 - (2 - κ) ^ 2) / (2 * Real.pi)
  have hηmin : 0 < ηmin :=
    (BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b) (by linarith) hκ
      (S.e_mem 0)).1
  have hηle : ∀ N, ηmin ≤ (boundaryZ b (S.e N)).im := fun N =>
    (BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b) (by linarith) hκ
      (S.e_mem N)).2
  have hρmin : 0 < ρmin := (semicircleDensity_ge' hκ (S.e_mem 0)).1
  have hρle : ∀ N, ρmin ≤ Parameters.semicircleDensity (S.e N) := fun N =>
    (semicircleDensity_ge' hκ (S.e_mem N)).2
  have hpi := Real.pi_pos
  set nq := ∑ i, ‖v i‖ ^ 2
  have hnq : 0 ≤ nq := by positivity
  have hWr : Tendsto (fun N => (S.W N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp S.tendsto_W
  have hWinv : Tendsto (fun N => ((S.W N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hWr
  set ν : ℕ → ℝ := fun N => Y / poleScale (S.W N) (S.e N)
  have hν0 : ∀ N, 0 ≤ ν N := fun N =>
    (div_pos hY (poleScale_pos (S.W_pos N) hκ (S.e_mem N))).le
  have hν : Tendsto ν atTop (𝓝 0) := by
    have hb' : Tendsto (fun N => (Y * ρmin⁻¹) * ((S.W N : ℝ))⁻¹) atTop (𝓝 0) := by
      simpa using hWinv.const_mul (Y * ρmin⁻¹)
    refine squeeze_zero hν0 (fun N => ?_) hb'
    have hW : (0 : ℝ) < S.W N := by exact_mod_cast S.W_pos N
    have hρ := hρle N
    simp only [ν, poleScale]
    rw [div_le_iff₀ (mul_pos hW (hρmin.trans_le hρ))]
    have : (Y * ρmin⁻¹) * ((S.W N : ℝ))⁻¹ * ((S.W N : ℝ) * Parameters.semicircleDensity (S.e N)) =
        Y * (Parameters.semicircleDensity (S.e N) / ρmin) := by
      field_simp
    rw [this]
    have h1 : 1 ≤ Parameters.semicircleDensity (S.e N) / ρmin := by
      rw [le_div_iff₀ hρmin]; linarith
    nlinarith
  set x : ℕ → ℝ := fun N => C * (matchedDistance b (S.e N) (S.X N) + ε (S.W N))
  have hx : Tendsto x atTop (𝓝 0) := by
    simpa [x] using (S.tendsto_d.add (hε.comp S.tendsto_W)).const_mul C
  have hev : ∀ᶠ N in atTop, W₀ ≤ S.W N ∧ matchedDistance b (S.e N) (S.X N) ≤ d₁ :=
    (S.tendsto_W.eventually_ge_atTop W₀).and (S.tendsto_d.eventually (Iic_mem_nhds hd₁))
  constructor
  · filter_upwards [hev] with N hN
    exact (hmain (S.W N) (S.W_pos N) hN.1 (S.e N) (S.e_mem N) (S.X N) (S.X_herm N) hN.2 r
      (S.J N) (S.J_frame N) v Y hY).1
  refine tendsto_of_window_bound (K := Real.pi / ηmin * nq) (B := B) (y := fun N => ν N * C₂)
    (x := x) (by positivity) hB hs₀ hx (by simpa using hν.mul_const C₂) ?_
  filter_upwards [hev] with N hN σ hσ hσs
  have h := (hmain (S.W N) (S.W_pos N) hN.1 (S.e N) (S.e_mem N) (S.X N) (S.X_herm N) hN.2 r
    (S.J N) (S.J_frame N) v Y hY).2 σ hσ hσs
  refine h.trans ?_
  have hd0 : 0 ≤ matchedDistance b (S.e N) (S.X N) := le_max_of_le_left (norm_nonneg _)
  have hpar : 0 ≤ C * (matchedDistance b (S.e N) (S.X N) + ε (S.W N)) + B * σ +
      Y / poleScale (S.W N) (S.e N) * (1 + σ⁻¹ ^ 2) * C₂ := by
    have := hε0 (S.W N); have := hν0 N; positivity
  have hle : Real.pi / (boundaryZ b (S.e N)).im * nq ≤ Real.pi / ηmin * nq :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hpi.le hηmin (hηle N)) hnq
  have heq : x N + B * σ + ν N * C₂ * (1 + σ⁻¹ ^ 2) =
      C * (matchedDistance b (S.e N) (S.X N) + ε (S.W N)) + B * σ +
        Y / poleScale (S.W N) (S.e N) * (1 + σ⁻¹ ^ 2) * C₂ := by
    simp only [x, ν]; ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hle hpar

/-- **`CollarMeanClause`** from `FreshPalmContract`, `PointDensityContract`,
`CommonPortMeanContract`, `TraceMatrixContract` and `PSSS.SourceContract`: along every admissible
old sequence, `E Im F_{W_n}(iY) → I_r` entrywise for every `Y > 0` (polarization of
`tendsto_collarMean_quad`).
-/
theorem collarMeanClause_of_inputs (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hCM : CommonPortMeanContract) (hTM : BlockBand.Internal.Contracts.Layers.TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) : CollarMeanClause := by
  intro b hb0 hb κ hκ r S Y hY i j
  set M : ∀ N, CollarSample (S.W N) → Matrix (Fin r) (Fin r) ℂ := fun N ω =>
    matrixImaginaryPart ((S.collarFns N ω).eval ((Y : ℂ) * Complex.I))
  set c : Fin 4 → ℂ := fun k => star (Complex.I ^ (k : ℕ))
  set g : Fin 4 → ∀ N, CollarSample (S.W N) → ℝ := fun k N ω =>
    (star (polVec i j k) ⬝ᵥ (M N ω *ᵥ polVec i j k)).re
  have hq := fun k => tendsto_collarMean_quad hP hPD hCM hTM source hb0 hb hκ S hY (polVec i j k)
  have hpt : ∀ N ω, M N ω i j = (1 / 4 : ℂ) * ∑ k, c k * ((g k N ω : ℝ) : ℂ) := by
    intro N ω
    rw [entry_eq_polarization (M N ω) i j]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c, g]
    rw [AtomicHerglotz.star_dotProduct_mulVec_ofReal_re (matrixImaginaryPart_isHermitian _)]
  have hint : ∀ᶠ N in atTop, ∀ k, Integrable (g k N) (collarLaw (S.W N) b) := by
    have h0 := (hq 0).1; have h1 := (hq 1).1; have h2 := (hq 2).1; have h3 := (hq 3).1
    filter_upwards [h0, h1, h2, h3] with N i0 i1 i2 i3 k
    fin_cases k
    · exact i0
    · exact i1
    · exact i2
    · exact i3
  have hEq : ∀ᶠ N in atTop, (1 / 4 : ℂ) * ∑ k, c k * ((∫ ω, g k N ω ∂collarLaw (S.W N) b : ℝ) : ℂ)
      = ∫ ω, M N ω i j ∂collarLaw (S.W N) b := by
    filter_upwards [hint] with N hN
    simp_rw [hpt N]
    rw [integral_const_mul, integral_finsetSum]
    · congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, integral_complex_ofReal]
    · intro k _
      exact ((hN k).ofReal (𝕜 := ℂ)).const_mul (c k)
  have hlim : Tendsto (fun N => (1 / 4 : ℂ) * ∑ k, c k *
      ((∫ ω, g k N ω ∂collarLaw (S.W N) b : ℝ) : ℂ)) atTop
      (𝓝 ((1 / 4 : ℂ) * ∑ k, c k * ((∑ a, ‖polVec i j k a‖ ^ 2 : ℝ) : ℂ))) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun k _ => Tendsto.const_mul _ ?_)
    exact (Complex.continuous_ofReal.tendsto _).comp (hq k).2
  have hone : (1 / 4 : ℂ) * ∑ k, c k * ((∑ a, ‖polVec i j k a‖ ^ 2 : ℝ) : ℂ) =
      (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
    rw [entry_eq_polarization (1 : Matrix (Fin r) (Fin r) ℂ) i j]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_mulVec, star_dotProduct_self_eq']
  rw [hone] at hlim
  exact hlim.congr' hEq

/-- `MatrixClosingStatement` from `CollarPolesClause` and the same inputs (mean clause
`collarMeanClause_of_inputs`, boundary clause `Boundary.collarBoundaryClause_of_exactBoundaryMean`
with `BoundaryMean.exactBoundaryMean_of_inputs`). `CollarPolesClause` fails at rank `0`, so this is
vacuous; the rank `≥ 1` form is `Poles.matrixClosing_of_clauses_pos`.
-/
theorem matrixClosing_of_poles_inputs (h1 : CollarPolesClause) (hP : FreshPalmContract)
    (hPD : PointDensityContract) (hCM : CommonPortMeanContract)
    (hTM : BlockBand.Internal.Contracts.Layers.TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) : MatrixClosingStatement :=
  Boundary.matrixClosing_of_poles_mean h1 (collarMeanClause_of_inputs hP hPD hCM hTM source)
    (BoundaryMean.exactBoundaryMean_of_inputs hP hPD hCM hTM source)

end BlockBand.Critical.MatrixClosing.Mean
