module

public import BlockBand.Transmission.LawFinite.CoreIter

/-!
# Entrance tools: one growth step under an integral, and positivity of `q₊`

* **`step_lintegral_le`**: Fubini over `pastLaw ⊗ freshLaw` for `∫ 1_S(past)·F(q_{r+1})`
  (the conditional step of without conditional expectations);
* `ae_passiveMass_freshSchur_pos`: `q(X) > 0` gives `q(X₊) > 0` a.s. (`Q₊ = L*QL`, `L`
  invertible); needed because `r_K(0) = 0` in Lean (`0⁻¹ = 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal

variable {W : ℕ}

/-- **One growth step under an integral** (Fubini over `pastLaw ⊗ freshLaw`): if a.s.
`X_{r+1} = freshSchur E (Xf(past_r)) fresh_r` and, for a.e. past sample in `S`, the fresh
integral of `F(q(X₊))` is at most `g(past)`, then
`∫ 1_S(past)·F(q_{r+1}) ≤ ∫ 1_S(past)·g(past)`. -/
theorem step_lintegral_le {b E : ℝ} (κ : ℝ → ℝ) (r : ℕ)
    {Xf : PastSample W r → Matrix (Fin W) (Fin W) ℂ} (hXf : Measurable Xf)
    (hae : ∀ᵐ ω ∂growthPathLaw W b, pathNearSchur b E κ W (r + 1) ω =
      freshSchur E (Xf (pastCoords W r ω)) (freshSample W r ω))
    {S : Set (PastSample W r)} (hS : MeasurableSet S) {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    {g : PastSample W r → ℝ≥0∞} (hg : Measurable g)
    (hb : ∀ᵐ p ∂pastLaw W r b, p ∈ S →
      ∫⁻ f, F (passiveMass b E (freshSchur E (Xf p) f)) ∂freshLaw W b ≤ g p) :
    ∫⁻ ω, (pastCoords W r ⁻¹' S).indicator
        (fun ω => F (passiveMass b E (pathNearSchur b E κ W (r + 1) ω))) ω ∂growthPathLaw W b ≤
      ∫⁻ ω, (pastCoords W r ⁻¹' S).indicator (fun ω => g (pastCoords W r ω)) ω
        ∂growthPathLaw W b := by
  set Ψ : PastSample W r × LayerSample W .oneBlockOnePort → ℝ≥0∞ :=
    fun q => S.indicator (fun p => F (passiveMass b E (freshSchur E (Xf p) q.2))) q.1
  have hΦ : Measurable fun q : PastSample W r × LayerSample W .oneBlockOnePort =>
      F (passiveMass b E (freshSchur E (Xf q.1) q.2)) :=
    hF.comp ((SourceMixing.measurable_passiveMass b E).comp
      (measurable_freshSchur_comp E (hXf.comp measurable_fst) measurable_snd))
  have hΨ : Measurable Ψ := by
    have : Ψ = (Prod.fst ⁻¹' S).indicator fun q => F (passiveMass b E (freshSchur E (Xf q.1) q.2)) := by
      funext q; by_cases h : q.1 ∈ S <;> simp [Ψ, Set.indicator, h]
    rw [this]; exact hΦ.indicator (measurable_fst hS)
  have hg' := (measurable_pastCoords W r).prodMk (measurable_freshSample W r)
  have h1 : ∫⁻ ω, (pastCoords W r ⁻¹' S).indicator
        (fun ω => F (passiveMass b E (pathNearSchur b E κ W (r + 1) ω))) ω ∂growthPathLaw W b =
      ∫⁻ ω, Ψ (pastCoords W r ω, freshSample W r ω) ∂growthPathLaw W b := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    by_cases h : pastCoords W r ω ∈ S <;> simp [Ψ, Set.indicator, h, hω]
  rw [h1, ← lintegral_map hΨ hg', growthPathLaw_map_past_fresh,
    lintegral_prod _ hΨ.aemeasurable]
  have h2 : ∫⁻ ω, (pastCoords W r ⁻¹' S).indicator (fun ω => g (pastCoords W r ω)) ω
      ∂growthPathLaw W b = ∫⁻ p, S.indicator g p ∂pastLaw W r b := by
    rw [← growthPathLaw_map_pastCoords, lintegral_map (hg.indicator hS) (measurable_pastCoords W r)]
    rfl
  rw [h2]
  refine lintegral_mono_ae ?_
  filter_upwards [hb] with p hp
  by_cases hpS : p ∈ S
  · simp only [Ψ, Set.indicator_of_mem hpS]; exact hp hpS
  · simp only [Ψ, Set.indicator_of_notMem hpS, lintegral_zero, le_refl]

/-- **Positivity of the fresh mass**: for a passive `X` with `q(X) > 0`, a.s. `q(X₊) > 0`
(`Q₊ = L*QL` with `L = -z⁻¹KS⁻¹B` invertible). -/
theorem ae_passiveMass_freshSchur_pos {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hq : 0 < passiveMass b E X) :
    ∀ᵐ f ∂freshLaw W b, 0 < passiveMass b E (freshSchur E X f) := by
  filter_upwards [PathScalar.ae_layer_herm (W := W) b,
    Bridge.ae_isUnit_layerLaw_bond hb0 hW .oneBlockOnePort,
    SourceMixing.ae_passiveQ_freshSchur hb0 hb hW h1 h2 hY] with f hA hB hQ
  have hzi : 0 < (boundaryZ b E).im := Bridge.boundaryZ_im_pos (by linarith) h1 h2
  have hz0 : boundaryZ b E ≠ 0 := fun h0 => by simp [h0] at hzi
  obtain ⟨hSu, -, h12⟩ := layer_blocks E hzi hY hA (hB 0 0)
  have hKR := (PassiveCovariance.nearPencil_inverse hb0 hb h1 h2 hY).1
  have hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) :=
    IsUnit.of_mul_eq_one _ hKR
  have hL : IsUnit (freshL b E X f).det := by
    have e : freshL b E X f = (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
        ((-(boundaryZ b E)⁻¹) • ((schurW E (boundaryZ b E) X f)⁻¹ * f.2 0 0)) := by
      rw [← h12]; rfl
    rw [e, det_mul, det_smul, det_mul]
    refine ((isUnit_iff_isUnit_det _).mp hK).mul (IsUnit.mul ?_ (IsUnit.mul ?_ ?_))
    · exact (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero hz0))).isUnit
    · exact (isUnit_iff_isUnit_det _).mp (Matrix.isUnit_nonsing_inv_iff.mpr hSu)
    · exact (isUnit_iff_isUnit_det _).mp (hB 0 0)
  set L := freshL b E X f
  set Q := passiveQ b E X
  have hQ0 : Q.PosSemidef := hY.conjTranspose_mul_mul_same _
  have hPS : (Lᴴ * Q * L).PosSemidef := hQ0.conjTranspose_mul_mul_same L
  by_contra hle
  push Not at hle
  have htr : (Lᴴ * Q * L).trace = 0 := by
    have h0 := hPS.trace_nonneg
    rw [Complex.nonneg_iff] at h0
    have hre : (Lᴴ * Q * L).trace.re = 0 := by
      have : passiveMass b E (freshSchur E X f) = (Lᴴ * Q * L).trace.re := by
        rw [passiveMass, hQ]
      linarith [h0.1]
    exact Complex.ext hre (by simpa using h0.2.symm)
  have hz : Lᴴ * Q * L = 0 := hPS.trace_eq_zero_iff.mp htr
  have hLL : L * L⁻¹ = 1 := mul_nonsing_inv _ hL
  have hQz : Q = (L⁻¹)ᴴ * (Lᴴ * Q * L) * L⁻¹ := by
    have : (L⁻¹)ᴴ * (Lᴴ * Q * L) * L⁻¹ = (L * L⁻¹)ᴴ * Q * (L * L⁻¹) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hLL, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  rw [hz, Matrix.mul_zero, Matrix.zero_mul] at hQz
  have : passiveMass b E X = 0 := by rw [passiveMass]; change Q.trace.re = 0; rw [hQz]; simp
  linarith

end BlockBand.Transmission.LawFinite
