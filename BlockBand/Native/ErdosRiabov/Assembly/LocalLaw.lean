module

public import BlockBand.Native.ErdosRiabov.Assembly.Extraction
public import BlockBand.Adapters.ErdosRiabov.ShortRingLocalLaw

/-!
# The short-ring local law from the zig conclusion

Assuming the conclusion of the zig step, the entrywise local law holds for the short-ring band
matrix. For the data `b, ζ₀, δ₀, κ, C₀, D` and `ε, D₁ > 0`:
* (1)–(2) the VS data `d = zigData …` with tolerance `ε/2`, so `ξ = min(ε/2, δ₀)/200` and
  `N^{ξ+ε/2} ≤ N^ε` for `N ≥ 1` (`rpow_zigData_le`); this is the zig proposition applied with
  `ε/2`, with `ξ` computed at the zig tolerance (`ξ ≤ ε/400 ≤ ε/2`);
* (3) `z = e + iη` lies in the bulk domain `𝒟` (`bulkDomain_of_contract`);
* (4)–(5) the zig hypothesis gives `P(Ψ^iso_{1,1} > N^{ξ+ε/2}) ≤ N^{-D₁}` under
  `driverLaw model.law`;
* (6) extraction and `shortRingLocalLaw_fin`: on
  `Fin (n W)`, `P(|G_ab(z) - m δ_ab| > N^{ξ+ε/2} Υ_η(a,b)^{1/2}) ≤ N^{-D₁}` for
  `H_1 = vsBandFin p 1`;
* (7) transport: `vsBandFin p 1 = reindex (siteFinEquiv p) (vsBand p 1)`
  (`vsBandFin_eq_reindex`), resolvent entries commute with the reindexing
  (`resolvent_reindex_apply`, from `Adapters.ErdosRiabov.resolvent_submatrix_apply`), the control
  at the physical sites is `siteControl` (`polynomialControl_siteFinEquiv`), and the law of
  `vsBand p 1` under `driverLaw model.law` is `model.law` (`VS.vsBand_law_one_model`).
  No separate law of the Erdős–Riabov ring matrix is needed, so `ringPhysMatrix` and
  `model_law_eq_ringPhys` are replaced by `VS.vsBand_law_one_model`.

`N₀` is the zig threshold at `(d, D₁)`; it depends only on the data and `(ε, D₁)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Assembly

open MeasureTheory
open BlockBand.External.ErdosRiabov (semicircleM)
open BlockBand.Internal.Contracts.Inputs (polynomialControl siteControl)
open BlockBand.Adapters.ErdosRiabov (siteFinEquiv)
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

/-!
### Constants (steps (1), (2))
-/

/-- The VS data of the contract data with the zig tolerance `ε/2`. -/
def zigData (b ζ₀ δ₀ κ C₀ D ε : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) (hδ : 0 < δ₀)
    (hδζ : δ₀ < ζ₀) (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) (hε : 0 < ε) : VSData where
  b := b
  delta0 := δ₀
  zeta0 := ζ₀
  kappa := κ
  C0 := C₀
  D := D
  eps := ε / 2
  b_pos := hb0
  b_lt_half := hb
  delta0_pos := hδ
  delta0_lt_zeta0 := hδζ
  kappa_pos := hκ
  C0_ge_one := hC₀
  D_ge_six := hD
  eps_pos := half_pos hε

/-- `ξ + ε/2 ≤ ε` for the zig data: `ξ = min(ε/2, δ₀)/200 ≤ ε/2`. -/
theorem zigData_xi_add_eps_le {b ζ₀ δ₀ κ C₀ D ε : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hδ : 0 < δ₀) (hδζ : δ₀ < ζ₀) (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) (hε : 0 < ε) :
    (zigData b ζ₀ δ₀ κ C₀ D ε hb0 hb hδ hδζ hκ hC₀ hD hε).xi +
        (zigData b ζ₀ δ₀ κ C₀ D ε hb0 hb hδ hδζ hκ hC₀ hD hε).eps ≤ ε := by
  simp only [VSData.xi, zigData]
  have := min_le_left (ε / 2) δ₀
  linarith

/-- `N^{ξ+ε/2} ≤ N^ε` for `N ≥ 1`. -/
theorem rpow_zigData_le {b ζ₀ δ₀ κ C₀ D ε : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hδ : 0 < δ₀) (hδζ : δ₀ < ζ₀) (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) (hε : 0 < ε)
    {N : ℝ} (hN : 1 ≤ N) :
    N ^ ((zigData b ζ₀ δ₀ κ C₀ D ε hb0 hb hδ hδζ hκ hC₀ hD hε).xi +
        (zigData b ζ₀ δ₀ κ C₀ D ε hb0 hb hδ hδζ hκ hC₀ hD hε).eps) ≤ N ^ ε :=
  Real.rpow_le_rpow_of_exponent_le hN (zigData_xi_add_eps_le hb0 hb hδ hδζ hκ hC₀ hD hε)

/-!
### The spectral parameter (step (3))
-/

/-- The contract box is the bulk domain: `z = e + iη` with `|e| ≤ 2 - κ`, `N^{-1+δ₀} ≤ η`,
`|z| ≤ C₀` lies in `𝒟 = BulkDomain N δ₀ κ C₀`. -/
theorem bulkDomain_of_contract {N : ℕ} {δ₀ κ C₀ e η : ℝ} (he : |e| ≤ 2 - κ)
    (hη : (N : ℝ) ^ (-1 + δ₀) ≤ η) (hz : ‖(e : ℂ) + (η : ℂ) * Complex.I‖ ≤ C₀) :
    BulkDomain N δ₀ κ C₀ ((e : ℂ) + (η : ℂ) * Complex.I) := by
  refine ⟨?_, ?_, hz⟩
  · simpa using he
  · simpa using hη

/-!
### The statement on `Fin (n W)`
-/

/-- **The local law on `Fin (n W)`, from `ZigConclusionK1`**: for the VS data `d` and
`D₁ > 0` there is `N₀` such that for every ring with `p.b = d.b`, `N = n W ≥ N₀`,
`N^{1+ζ₀} ≤ W²`, every model, every `z ∈ 𝒟` and all `a, b : Fin N`, under `driverLaw model.law`,
`P(N^{ξ+ε} Υ_η(a,b)^{1/2} < |G_ab(z) - m δ_ab|) ≤ N^{-D₁}` for `G = (H_1 - z)⁻¹`,
`H_1 = vsBandFin p 1`, `η = Im z`, `Υ = polynomialControl N W D`.
-/
theorem shortRingLocalLaw_fin (hzig : ZigConclusionK1) (d : VSData) (D₁ : ℝ) (hD₁ : 0 < D₁) :
    ∃ N₀ : ℕ, ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ),
        BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z → ∀ a b : Fin (p.n * p.W),
        driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
            {x | ((p.n * p.W : ℕ) : ℝ) ^ (d.xi + d.eps) *
                Real.sqrt (polynomialControl (p.n * p.W) p.W d.D z.im a b) <
              ‖(VS.vsBandFin p 1 x -
                  z • (1 : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ))⁻¹ a b -
                (if a = b then semicircleM z else 0)‖} ≤
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D₁)) := by
  obtain ⟨N₀, hN₀⟩ := hzig d D₁ hD₁
  refine ⟨N₀, fun p hpb hN hband model z hz a b => ?_⟩
  have hzim : 0 < z.im := hz.im_pos (Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos)
  refine (measure_mono fun x hx => ?_).trans (hN₀ p hpb hN hband model z hz)
  exact extraction_zig p d.D hzim hx

/-!
### Transport from `Fin (n W)` to the physical sites
-/

theorem vsBandFin_eq_reindex (p : BlockBand.Parameters) (t : ℝ≥0) (x : RingSample p) :
    VS.vsBandFin p t x =
      Matrix.reindex (VS.ringSiteEquiv p) (VS.ringSiteEquiv p) (VS.vsBand p t x) :=
  VS.ringMatrixFin_apply p _

/-- Resolvent entries commute with reindexing by an equivalence. -/
theorem resolvent_reindex_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι ι ℂ) (e : ι ≃ κ) (z : ℂ) (x y : ι) :
    (Matrix.reindex e e A - z • (1 : Matrix κ κ ℂ))⁻¹ (e x) (e y) =
      (A - z • (1 : Matrix ι ι ℂ))⁻¹ x y := by
  have h := Adapters.ErdosRiabov.resolvent_submatrix_apply (Matrix.reindex e e A) e z x y
  have hA : (Matrix.reindex e e A).submatrix e e = A := by
    ext i j
    simp [Matrix.reindex_apply]
  rw [hA] at h
  exact h.symm

/-- **Transport, event form**: the bad event of `H_1 = vsBand p 1` at physical sites `x, y`
(threshold `X`, height `η = Im z`) is the bad event of `vsBandFin p 1` at the corresponding
indices `VS.ringSiteEquiv p x`, `VS.ringSiteEquiv p y`. -/
theorem transport_event (p : BlockBand.Parameters) (D X : ℝ) (z : ℂ) (x y : p.Site) :
    VS.vsBand p 1 ⁻¹' {H : p.SiteMatrix | X * Real.sqrt (siteControl p D z.im x y) <
        ‖(H - z • (1 : p.SiteMatrix))⁻¹ x y - (if x = y then semicircleM z else 0)‖} =
      {ω | X * Real.sqrt (polynomialControl (p.n * p.W) p.W D z.im
            (VS.ringSiteEquiv p x) (VS.ringSiteEquiv p y)) <
          ‖(VS.vsBandFin p 1 ω -
              z • (1 : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ))⁻¹
              (VS.ringSiteEquiv p x) (VS.ringSiteEquiv p y) -
            (if VS.ringSiteEquiv p x = VS.ringSiteEquiv p y then semicircleM z else 0)‖} := by
  ext ω
  have hc : polynomialControl (p.n * p.W) p.W D z.im (VS.ringSiteEquiv p x)
      (VS.ringSiteEquiv p y) = siteControl p D z.im x y :=
    Adapters.ErdosRiabov.polynomialControl_siteFinEquiv p D z.im x y
  have hxy : (VS.ringSiteEquiv p x = VS.ringSiteEquiv p y) ↔ (x = y) :=
    (VS.ringSiteEquiv p).injective.eq_iff
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hc, hxy, vsBandFin_eq_reindex,
    resolvent_reindex_apply]

/-!
### The local law, conditional on the zig conclusion
-/

/-- **`ShortRingLocalLaw` from the zig conclusion.** The statement
`BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw` from the hypothesis
`ZigConclusionK1`. The proof follows steps (1)–(7) of the module docstring: zig data with
tolerance `ε/2`
(`N^{ξ+ε/2} ≤ N^ε`), extraction at `t = 1`, the `Fin`-world bound, transport to
the physical sites and the terminal law `law(H_1) = model.law`.
`N₀` is the zig
threshold at the zig data and `D₁`.
-/
theorem shortRingLocalLaw_of_zig (hzig : ZigConclusionK1) :
    BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw := by
  intro b ζ₀ δ₀ κ C₀ hb0 hb hδ hδζ hκ hC₀ D hD ε D₁ hε hD₁
  set d := zigData b ζ₀ δ₀ κ C₀ D ε hb0 hb hδ hδζ hκ hC₀ hD hε with hd
  obtain ⟨N₀, hN₀⟩ := shortRingLocalLaw_fin hzig d D₁ hD₁
  refine ⟨N₀, fun p hpb hN hband model e η he hη hz x y => ?_⟩
  set z : ℂ := (e : ℂ) + (η : ℂ) * Complex.I with hzdef
  have hzim : z.im = η := by simp [hzdef]
  have hzB : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z := bulkDomain_of_contract he hη hz
  have hN1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast p.N_pos
  have hX : ((p.n * p.W : ℕ) : ℝ) ^ (d.xi + d.eps) ≤ ((p.n * p.W : ℕ) : ℝ) ^ ε :=
    rpow_zigData_le hb0 hb hδ hδζ hκ hC₀ hD hε hN1
  have hfin := hN₀ p hpb hN hband model z hzB (VS.ringSiteEquiv p x) (VS.ringSiteEquiv p y)
  set E : Set p.SiteMatrix := {H | (p.N : ℝ) ^ ε * Real.sqrt (siteControl p D η x y) <
      ‖(H - z • (1 : p.SiteMatrix))⁻¹ x y - (if x = y then semicircleM z else 0)‖} with hE
  have hmeas : MeasurableSet E :=
    Adapters.ErdosRiabov.measurableSet_resolventBad p _ z _ x y
  have hsub : VS.vsBand p 1 ⁻¹' E ⊆
      VS.vsBand p 1 ⁻¹' {H : p.SiteMatrix |
        ((p.n * p.W : ℕ) : ℝ) ^ (d.xi + d.eps) * Real.sqrt (siteControl p d.D z.im x y) <
          ‖(H - z • (1 : p.SiteMatrix))⁻¹ x y - (if x = y then semicircleM z else 0)‖} := by
    intro ω hω
    simp only [Set.mem_preimage, hE, Set.mem_ofPred_eq] at hω ⊢
    rw [hzim]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hX (Real.sqrt_nonneg _)) hω
  rw [transport_event] at hsub
  calc (model.law : Measure p.SiteMatrix) E
      = Measure.map (VS.vsBand p 1)
          (driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)) E := by
        rw [VS.vsBand_law_one_model]
    _ = driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
          (VS.vsBand p 1 ⁻¹' E) := Measure.map_apply (VS.measurable_vsBand p 1) hmeas
    _ ≤ _ := (measure_mono hsub).trans hfin

/-- **`ShortRingLocalLaw` from the zig proposition**: the statement from the hypothesis
`ZigConclusion` (which is proved from `SatLin.masterIneqSat` through
`ZigProof.zigConclusion_of_masterIneq`).
-/
theorem shortRingLocalLaw_of_zigConclusion (hzig : ZigConclusion) :
    BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw :=
  shortRingLocalLaw_of_zig (zigConclusionK1_of_zigConclusion hzig)

end BlockBand.Native.ErdosRiabov.Assembly
