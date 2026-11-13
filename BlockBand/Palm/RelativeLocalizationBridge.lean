module

public import BlockBand.Palm.RelativeLocalizationKh
public import BlockBand.Palm.RelativeLocalizationGapProb

/-!
# Relative localization: arbitrary solutions are the adapted mass on the good event

Every solution of the forward mass equation whose coefficients are a continuous function of the
eigenvalue path agrees with the adapted mass `genMass` (`genMass_eq_solution`); on paths with a
uniform eigenvalue gap, the reference and short generators equal their truncated versions
`truncRefGen` and `truncShortGen`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory Set BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal

variable {N : ℕ}

theorem forwardMass_shift_start {L : ℝ → Fin N → Fin N → ℝ} {s u : ℝ} {v₀ : Fin N → ℝ}
    {v : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L s u v₀ v) :
    ForwardMassSolution (fun x => L (x + s)) 0 (u - s) v₀ (fun x => v (x + s)) := by
  obtain ⟨h0, hc, hd⟩ := hv
  refine ⟨by simp [h0], ?_, fun x hx => ?_⟩
  · refine hc.comp (continuous_id.add continuous_const).continuousOn fun x hx => ⟨?_, ?_⟩
    · linarith [hx.1]
    · linarith [hx.2]
  · have := hd (x + s) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact HasDerivAt.comp_add_const x s this

theorem genMass_eq_solution {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s u : ℝ} (has : a ≤ s)
    {ω : FlowSample N} {L : ℝ → Fin N → Fin N → ℝ}
    (hL : ∀ σ ∈ Ioo s u, L σ = Gen (flowLam F (Real.toNNReal (σ - a)) ω))
    {v₀ : FlowSample N → Fin N → ℝ} {v : ℝ → Fin N → ℝ}
    (hv : ForwardMassSolution L s u (v₀ ω) v) {r : ℝ} (hr : r ∈ Icc 0 (u - s)) :
    genMass Gen F (Real.toNNReal (s - a)) v₀ (Real.toNNReal r) ω = v (r + s) := by
  have hw := forwardMass_shift_start hv
  have hw' := forwardMass_congr hw
    (L' := realCoeff (genCoeff Gen F (Real.toNNReal (s - a))) ω) (fun x hx => by
      simp only [realCoeff, genCoeff]
      rw [hL (x + s) ⟨by linarith [hx.1], by linarith [hx.2]⟩]
      congr 2
      rw [show x + s - a = (s - a) + x by ring,
        Real.toNNReal_add (by linarith) hx.1.le])
  have := adaptedMass_eq (genCoeff_continuous hG hF _) v₀ ω hw' hr
  simp only [genMass]
  rw [Real.coe_toNNReal _ hr.1]
  exact this

theorem flowLam_eq_at {F : Matrix (Fin N) (Fin N) ℂ} {a σ : ℝ} (haσ : a ≤ σ) {ω : FlowSample N}
    (hω : ω.1.IsHermitian) :
    flowEigenvalue F a ω σ = flowLam F (Real.toNNReal (σ - a)) ω := by
  rw [flowLam_eq_flowEigenvalue F a hω, Real.coe_toNNReal _ (by linarith)]
  congr 1; ring_nf

theorem referenceGenerator_eq_trunc {F : Matrix (Fin N) (Fin N) ℂ} {a b₀ σ : ℝ} (haσ : a ≤ σ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {g : ℝ} (hg : 0 ≤ g)
    (hgap : ∀ k m : Fin N, k ≠ m →
      g ≤ |flowLam F (Real.toNNReal (σ - a)) ω k - flowLam F (Real.toNNReal (σ - a)) ω m|) :
    referenceGenerator F a b₀ ω ℓ σ = truncRefGen N (flowLam F (Real.toNNReal (σ - a)) ω) ℓ b₀ g := by
  rw [referenceGenerator_eq_refGen, flowLam_eq_at haσ hω, truncRefGen_eq hℓ hg hgap]

theorem shortGenerator_eq_trunc {F : Matrix (Fin N) (Fin N) ℂ} {a σ : ℝ} (haσ : a ≤ σ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) {ℓ : ℕ} {g : ℝ} (hg : 0 ≤ g)
    (hgap : ∀ k m : Fin N, k ≠ m →
      g ≤ |flowLam F (Real.toNNReal (σ - a)) ω k - flowLam F (Real.toNNReal (σ - a)) ω m|) :
    shortGenerator F a ω ℓ σ = truncShortGen N (flowLam F (Real.toNNReal (σ - a)) ω) ℓ g := by
  rw [shortGenerator_eq_shortGen, flowLam_eq_at haσ hω, truncShortGen_eq hg hgap]

end BlockBand.Palm.RelativeLocalization
