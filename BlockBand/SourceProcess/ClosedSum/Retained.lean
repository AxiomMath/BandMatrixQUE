module

public import BlockBand.SourceProcess.ClosedSum.PerfNull
public import BlockBand.SourceProcess.ClosedPath.TimeSMain
public import BlockBand.SourceProcess.ClosingAux.Contraction

/-!
# No retained far mode is perfectly transmitted, almost surely

* `physTseq_eq` (every `ω`, `k < W`): `t_k = 1 - ‖S_ff f_k‖²`; hence `physTseq_le_one`, and
  `physTseq_lt_one` when `S_ff` is injective.
* **`ae_farReflection_injective`** (`b < 1/2`, `-2 < E < 2`, `W ≥ 1`): almost surely, for every
  length `n`, the far reflection block `S_ff(n)` is injective. From `farReflection_ker` and the
  a.s. invertibility of `modPencil E z⁻¹ z̄⁻¹` (`ae_isUnit_modPencil`). This is the far–far
  statement, not the near–far `corner_injective`.
* **`ae_hlt`**: almost surely, the hypothesis `hlt` (no retained far mode is perfectly
  transmitted) holds for every `K` and `h`.
* `isTransmissionSequence_physTseq`: if `𝕊(n_s)𝕊(n_s)ᴴ = 1`, `physTseq` is a
  transmission sequence (antitone, in `[0,1]`, summable).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingAux
open scoped ComplexOrder

variable {W : ℕ} {b E s : ℝ}

/-- **`S_ff(n)` is injective at every length, almost surely.** -/
theorem ae_farReflection_injective (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ n (v : Fin W → ℂ), farReflection b E W n ω *ᵥ v = 0 → v = 0 := by
  have hη : 0 < (boundaryZ b E).im := boundaryZ_im_pos (by linarith) hE1 hE2
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  filter_upwards [ae_growth_isHermitian W b, ae_isUnit_pathPencil_growth hb hW E,
    ae_isUnit_modPencil hb hW E (boundaryZ b E)⁻¹ (star (boundaryZ b E))⁻¹] with ω hA hF hG n v hv
  exact farReflection_ker b E ω (isUnit_fullPathMatrix b E n ω hA hη (hF n)) hz (hG n) hv

theorem physFarVec_unit {ω : GrowthPath W} {k : ℕ} (hk : k < Fintype.card (Fin W)) :
    star (physFarVec b E s W ω k) ⬝ᵥ physFarVec b E s W ω k = 1 := by
  rw [physFarVec_orthonormal hk hk]; simp

/-- `t_k = 1 - ‖S_ff f_k‖²`. -/
theorem physTseq_eq (ω : GrowthPath W) {k : ℕ} (hk : k < Fintype.card (Fin W)) :
    ((physTseq b E s W ω k : ℝ) : ℂ) = 1 -
      star (farReflection b E W (closeLen s W) ω *ᵥ physFarVec b E s W ω k) ⬝ᵥ
        (farReflection b E W (closeLen s W) ω *ᵥ physFarVec b E s W ω k) := by
  have e := congrArg (fun x => star (physFarVec b E s W ω k) ⬝ᵥ x)
    (farTransmission_mulVec_physFarVec (b := b) (E := E) (s := s) (ω := ω) k)
  simp only [dotProduct_smul, physFarVec_unit hk, smul_eq_mul, mul_one] at e
  rw [← e, quad_mulVec, farTransmission, sub_mulVec, one_mulVec, dotProduct_sub,
    physFarVec_unit hk]

theorem quad_re_nonneg (x : Fin W → ℂ) : 0 ≤ (star x ⬝ᵥ x).re :=
  (Complex.nonneg_iff.1 (dotProduct_star_self_nonneg x)).1

theorem physTseq_le_one (ω : GrowthPath W) (k : ℕ) : physTseq b E s W ω k ≤ 1 := by
  by_cases hk : k < Fintype.card (Fin W)
  · have e := congrArg Complex.re (physTseq_eq (b := b) (E := E) (s := s) ω hk)
    simp only [Complex.ofReal_re, Complex.sub_re, Complex.one_re] at e
    linarith [quad_re_nonneg (farReflection b E W (closeLen s W) ω *ᵥ physFarVec b E s W ω k)]
  · simp only [physTseq, hk, ↓reduceDIte]; norm_num

theorem physTseq_lt_one {ω : GrowthPath W}
    (hinj : ∀ v : Fin W → ℂ, farReflection b E W (closeLen s W) ω *ᵥ v = 0 → v = 0) {k : ℕ}
    (hk : k < Fintype.card (Fin W)) : physTseq b E s W ω k < 1 := by
  by_contra hge
  set y := farReflection b E W (closeLen s W) ω *ᵥ physFarVec b E s W ω k
  have e := congrArg Complex.re (physTseq_eq (b := b) (E := E) (s := s) ω hk)
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.one_re] at e
  have hre : (star y ⬝ᵥ y).re ≤ 0 := by linarith [not_lt.1 hge]
  have hy : y = 0 := dotProduct_star_self_eq_zero.1
    (re_eq_zero_of_nonneg (dotProduct_star_self_nonneg y) hre)
  have h0 := hinj _ hy
  have h1 := physFarVec_unit (b := b) (E := E) (s := s) (ω := ω) hk
  rw [h0, dotProduct_zero] at h1
  exact zero_ne_one h1

/-- **The hypothesis `hlt` holds almost surely**, for every cap `K` and cutoff `h`. -/
theorem ae_hlt (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (K : ℕ) (h : ℝ) (k : Fin K),
      h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1 := by
  filter_upwards [ae_farReflection_injective hb hE1 hE2 hW] with ω hinj K h k hk
  exact physTseq_lt_one (hinj _) (retained_lt_card hk)

theorem physTseq_nonneg {ω : GrowthPath W}
    (hS : scatteringMatrix b E W (closeLen s W) ω * (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1)
    (k : ℕ) : 0 ≤ physTseq b E s W ω k := by
  by_cases hk : k < Fintype.card (Fin W)
  · have e := congrArg (fun x => star (physFarVec b E s W ω k) ⬝ᵥ x)
      (farTransmission_mulVec_physFarVec (b := b) (E := E) (s := s) (ω := ω) k)
    simp only [dotProduct_smul, physFarVec_unit hk, smul_eq_mul, mul_one] at e
    rw [farTransmission_eq_of_unitary (mul_eq_one_comm.mp hS), ← quad_mulVec] at e
    have := congrArg Complex.re e
    simp only [Complex.ofReal_re] at this
    rw [← this]; exact quad_re_nonneg _
  · simp only [physTseq, hk, ↓reduceDIte, le_refl]

/-- **`physTseq` is a transmission sequence**, given unitarity at `n_s`. -/
theorem isTransmissionSequence_physTseq {ω : GrowthPath W}
    (hS : scatteringMatrix b E W (closeLen s W) ω * (scatteringMatrix b E W (closeLen s W) ω)ᴴ = 1) :
    IsTransmissionSequence (physTseq b E s W ω) := by
  refine ⟨fun k l hkl => ?_, fun k => ⟨physTseq_nonneg hS k, physTseq_le_one ω k⟩,
    summable_of_ne_finset_zero (s := Finset.range (Fintype.card (Fin W))) fun k hk => ?_⟩
  · by_cases hl : l < Fintype.card (Fin W)
    · have hk : k < Fintype.card (Fin W) := lt_of_le_of_lt hkl hl
      simp only [physTseq, hk, hl, ↓reduceDIte]
      exact (isHermitian_farTransmission b E W (closeLen s W) ω).eigenvalues₀_antitone
        (Fin.mk_le_mk.2 hkl)
    · simp only [physTseq, hl, ↓reduceDIte]
      have := physTseq_nonneg hS k
      simpa only [physTseq] using this
  · rw [Finset.mem_range] at hk
    simp only [physTseq, hk, ↓reduceDIte]

end BlockBand.SourceProcess.ClosedSum
