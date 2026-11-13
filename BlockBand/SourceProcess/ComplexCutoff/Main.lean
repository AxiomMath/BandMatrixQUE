module

public import BlockBand.SourceProcess.ComplexCutoff.Estimate
public import BlockBand.SourceProcess.CutoffLimit.Main

/-!
# `ComplexCutoffRemoval` from the two coupling hypotheses

The target is `ComplexConstruct.ComplexCutoffRemoval`.

* The uniform cutoff estimate (inside `complexCutoffRemoval_of`): for every `ε₀ > 0` there is `h₀ > 0` with
  `|Ψ(K,h₁) − Ψ(K,h₂)| ≤ ε₀` for all `0 < h₁ ≤ h₂ < h₀` and **all caps `K`**. Proof: the coupling
  of `CoupledComplexCutoff`, `abs_sub_le`, the trace and rank-free bounds for the frames, and
  the extended coupling `ExtendedRankFreeCoupling` for `𝒦`; `E R₀ + 2B ≤ 8Γ + 2Σ d_*m_j` is
  finite by the `fractional` field of `TransmissionLawContract`, and
  `E X₀ ≤ 4 E∫ψ_{1/2}1_{y ≤ h₂²} → 0` (`tendsto_tail`).
  Choose the trace level `L`, the `𝒦` level `L_𝒦`, the box `Λ`, the modulus `δ`, then
  `δ_𝒦, u, u₄`, then `h₀`. Then `K → ∞` and `exists_tendsto_of_uniform`.
* `complexCutoffRemoval_holds`: the same from the Gaussian inputs and `MatchedTracesContract`.
* `complexModelExists_of_coupled`: the coupling hypothesis is at least `ComplexModelExists`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCutoff

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourcePins
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.CutoffLimit BlockBand.SourceProcess.ComplexConstruct
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs BlockBand.SourceProcess.BornUnique
open scoped ENNReal NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

theorem div_div_add_one_le {a η : ℝ} (ha : 0 ≤ a) (hη : 0 < η) : a / (a / η + 1) ≤ η := by
  rw [div_le_iff₀ (by positivity), mul_add, mul_div_cancel₀ _ hη.ne', mul_one]
  linarith

theorem mul_div_add_one_div_le {a η d : ℝ} (ha : 0 ≤ a) (hη : 0 < η) (hd : 0 < d) :
    a * (η * d / (a + 1)) / d ≤ η := by
  rw [div_le_iff₀ hd, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hη hd]

theorem ofReal_C_le {C a b η : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h : |C| * a / b ≤ η) :
    ENNReal.ofReal (C * a / b) ≤ ENNReal.ofReal η := by
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ h)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) ha) hb.le

/-- **`ComplexCutoffRemoval`** from
`TransmissionLawContract` and the two open coupling hypotheses. -/
theorem complexCutoffRemoval_of (hTL : TransmissionLawContract) (hA : CoupledComplexCutoff)
    (hB : ExtendedRankFreeCoupling) : ComplexCutoffRemoval := by
  intro b E np τ m T hD Ω _ P μ hlim s hs hsτ Φ Ψ Λf hΨ hΛf
  have hb0 : 0 < b := hD.1
  have hb : b < 1 / 2 := hD.2.1
  have hE1 : -2 < E := hD.2.2.1
  have hE2 : E < 2 := hD.2.2.2.1
  obtain ⟨ρ, hρ, hρs, hρe⟩ :=
    entrance_sequence (entranceAtomic_of hTL) seqExtraction_holds hb0 hb hE1 hE2 hlim hs
  have hΓ := lintegral_entrance_psi_lt_top hTL hb0 hb hE1 hE2 hlim hs
  have htl := tendsto_tail hΓ
  obtain ⟨Cf, hCf⟩ := hB (transportD0 b E) (etaZ b E)
  have hD0 := transportD0_pos' hb0 hE1 hE2
  set ent := entranceLaw P μ s
  set t := (T - s).toNNReal
  set A : ℝ≥0∞ := 8 * (∫⁻ ν, ∫⁻ y, psiP (1 / 2) y ∂ν ∂ent) +
    ENNReal.ofReal (2 * ∑ j, dStar b * m j) with hAdef
  have hA' : A ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hΓ.ne,
    ENNReal.ofReal_ne_top⟩
  refine exists_tendsto_of_uniform Λf fun ε₀ hε₀ => ?_
  have hΦ0 := norm_nonneg Φ
  set η := ε₀ / (18 * (2 * ‖Φ‖ + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hε : 0 < ε₀ / 2 := by positivity
  obtain ⟨lv, hlv, hAlv⟩ := exists_div_le hA' hη
  set c := |Cf lv| * (t : ℝ) with hcdef
  have hc0 : 0 ≤ c := by positivity
  set Lk := c / η + 1 with hLk
  have hLk0 : 0 < Lk := by positivity
  set J := kBirthJump E (fun j => τ j - s) m (t : ℝ)
  set Λ := ‖J‖ + Real.sqrt Lk + 1 + lv + lv ^ 2
  obtain ⟨δ, hδ0, hδ⟩ := exists_modulus Φ Λ (ε₀ / 2) hε
  set mδ := min δ 1
  have hm0 : 0 < mδ := lt_min hδ0 one_pos
  set δk := (mδ / 4) ^ 2 with hδkdef
  have hδk : 0 < δk := by positivity
  have hsδk : Real.sqrt δk = mδ / 4 := Real.sqrt_sq (by positivity)
  set r := mδ / (4 * ((Real.sqrt lv + 1) * (1 + 2 * lv)))
  have hr : 0 < r := by positivity
  set u := r ^ 2
  have hu : 0 < u := by positivity
  have hsu : Real.sqrt u = r := Real.sqrt_sq hr.le
  set u₄ := η * δk / (c + 1)
  have hu₄ : 0 < u₄ := by positivity
  have hΛ : ‖J‖ + Real.sqrt Lk + Real.sqrt δk + lv + lv ^ 2 ≤ Λ := by
    have : mδ ≤ 1 := min_le_right _ _
    rw [hsδk]; linarith
  have hδΛ : Real.sqrt δk + Real.sqrt u * (2 * Real.sqrt lv) * (1 + 2 * lv) < δ := by
    rw [hsδk, hsu]
    have h1 : r * (2 * Real.sqrt lv) * (1 + 2 * lv) ≤ mδ / 2 := by
      have hq : 0 < (Real.sqrt lv + 1) * (1 + 2 * lv) := by positivity
      have e : r * (2 * ((Real.sqrt lv + 1) * (1 + 2 * lv))) = mδ / 2 := by
        simp only [r]; field_simp; ring
      have : r * (2 * Real.sqrt lv) * (1 + 2 * lv) ≤
          r * (2 * ((Real.sqrt lv + 1) * (1 + 2 * lv))) := by
        have := Real.sqrt_nonneg lv
        nlinarith
      linarith
    have : mδ ≤ δ := min_le_left _ _
    linarith
  set ec := Real.exp (transportD0 b E * lv ^ 2 * (t : ℝ) / 2)
  have hec : 0 < ec := Real.exp_pos _
  have hθ : (0 : ℝ≥0∞) < ENNReal.ofReal (η * min u u₄ / (4 * ec)) :=
    ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨n, hn⟩ := (htl.eventually (gt_mem_nhds hθ)).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun x y hx hxy hy => ?_⟩
  have hy0 : 0 < y := hx.trans_le hxy
  have hlim' : Tendsto (fun K => Ψ K x - Ψ K y) atTop (𝓝 (Λf x - Λf y)) :=
    (hΛf x hx).sub (hΛf y hy0)
  refine le_of_tendsto hlim'.abs (Eventually.of_forall fun K => ?_)
  obtain ⟨ι, S, _, _, _, μ', _, Naux, P', Emb, 𝓖, tseq, nb, tb, col, w, β, X₁, X₂, Y₁, Y₂, hC⟩ :=
    hA b E np τ m T hD s hs hsτ ρ hρ hρs x y K hx hxy
  rw [hρe] at hC
  have I0 := hC.initTrace_add_le
  have I2 := hC.initDist_le hx.le hxy
  have htail : (∫⁻ ν, ∫⁻ z, tailPsi y z ∂ν ∂ent) ≤
      ENNReal.ofReal (η * min u u₄ / (4 * ec)) :=
    (lintegral_mono fun ν => lintegral_mono (tailPsi_mono hy0.le hy.le)).trans hn.le
  have hX0 : ∀ v : ℝ, 0 < v → min u u₄ ≤ v →
      ENNReal.ofReal ec * initDist' μ' Emb tseq np x y / ENNReal.ofReal v ≤ ENNReal.ofReal η := by
    intro v hv hmv
    rw [← ofReal_mul_div_eq hec hv hη]
    gcongr
    refine I2.trans (mul_le_mul_right (htail.trans (ENNReal.ofReal_le_ofReal ?_)) 4)
    gcongr
  have q0 := (ENNReal.div_le_div_right I0 (ENNReal.ofReal lv)).trans hAlv
  have p1 := (hC.meas_trace_le hb0 hE1 hE2 t hlv).trans q0
  have p2 := (hC.meas_dist_le hb0 hE1 hE2 t hlv hu).trans
    (add_le_add q0 (hX0 u hu (min_le_left _ _)))
  have hB' := hCf ι (SrcCol K (Fin np)) S μ' Naux P' (srcSignature K (Fin np)) hD0 hC.nearProj
    (isSignature_srcSignature K _) _ _ hC.frame₁_meas hC.frame₂_meas hC.frame₁_two hC.frame₂_two
    nb tb col w β hC.stopping hC.birth_meas hC.col_inj hC.col_sig hC.col_zero hC.birth_near X₁ X₂
    hC.sol₁ hC.sol₂ hC.perp Y₁ Y₂ hC.kSol₁ hC.kSol₂
  have p3 := (hB' lv u Lk t hlv hu hLk0).2.trans (add_le_add q0
    (ofReal_C_le t.2 hLk0 (div_div_add_one_le hc0 hη)))
  have q4 : 2 * ((∫⁻ z, ENNReal.ofReal (hsSq (cutFrame (Fin np) Emb tseq x z) +
      hsSq (cutFrame (Fin np) Emb tseq y z)) ∂driverLaw (κ := SourceNoise ι) μ') +
        ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal lv ≤ 2 * ENNReal.ofReal η := by
    rw [mul_div_assoc]
    exact mul_le_mul_right q0 2
  have q5 : ENNReal.ofReal (Cf lv * u₄ * (t : ℝ) / δk) ≤ ENNReal.ofReal η := by
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ (mul_div_add_one_div_le hc0 hη hδk))
    refine div_le_div_of_nonneg_right ?_ hδk.le
    have : Cf lv * (t : ℝ) ≤ c := mul_le_mul_of_nonneg_right (le_abs_self _) t.2
    nlinarith
  have p4 := (hB' lv u₄ δk t hlv hu₄ hδk).1.trans
    (add_le_add (add_le_add q4 (hX0 u₄ hu₄ (min_le_right _ _))) q5)
  have hsum := add_le_add (add_le_add (add_le_add p1 p2) p3) p4
  have h9 : ENNReal.ofReal η + (ENNReal.ofReal η + ENNReal.ofReal η) +
      (ENNReal.ofReal η + ENNReal.ofReal η) +
      (2 * ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η) = 9 * ENNReal.ofReal η := by
    ring
  rw [h9] at hsum
  have H := hC.abs_sub_le Φ hε hδ hΛ hδΛ (hΨ K x hx) (hΨ K y hy0)
  have hfin : ENNReal.ofReal (2 * ‖Φ‖) * (9 * ENNReal.ofReal η) ≤ ENNReal.ofReal (ε₀ / 2) := by
    rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : 2 * ‖Φ‖ * (9 * η) = ‖Φ‖ * ε₀ / (2 * ‖Φ‖ + 1) := by
      rw [hηdef]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have tot := H.trans (add_le_add le_rfl ((mul_le_mul_right hsum _).trans hfin))
  rw [← ENNReal.ofReal_add hε.le hε.le, add_halves] at tot
  exact (ENNReal.ofReal_le_ofReal_iff hε₀.le).1 tot

/-- **`ComplexCutoffRemoval` from `MatchedTracesContract` and the Gaussian inputs**, and the
two open coupling hypotheses. -/
theorem complexCutoffRemoval_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hA : CoupledComplexCutoff) (hB : ExtendedRankFreeCoupling) : ComplexCutoffRemoval :=
  complexCutoffRemoval_of (Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP)
    hA hB

/-- The coupling hypothesis is at least `ComplexModelExists` (take `h₁ = h₂ = h` and the first model). -/
theorem complexModelExists_of_coupled (hA : CoupledComplexCutoff) : ComplexModelExists := by
  intro b E np τ m T hD s hs hsτ ρ hρ hρs h K hh
  obtain ⟨ι, S, _, _, _, μ, _, Naux, P, Emb, 𝓖, tseq, nb, tb, col, w, β, X₁, X₂, Y₁, Y₂, hC⟩ :=
    hA b E np τ m T hD s hs hsτ ρ hρ hρs h h K hh le_rfl
  exact ⟨DriverSample S (SourceNoise ι), inferInstance, 𝓖, driverLaw (κ := SourceNoise ι) μ, tseq,
    fun t x => gramPair P (X₁ t x), kProc E s τ m Y₁, hC.model₁⟩

end BlockBand.SourceProcess.ComplexCutoff
