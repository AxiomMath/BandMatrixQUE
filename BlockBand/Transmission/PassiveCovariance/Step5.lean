module

public import BlockBand.Transmission.PassiveCovariance.WordReduction
public import BlockBand.Transmission.PassiveCovariance.StationaryJet
public import BlockBand.Transmission.PassiveCovariance.Step5Algebra

/-!
# The replica scalars of the passive covariance

The ladder scalars simplify to `r = c₀(σ₋ - σ₊)` and `r₁₂ = (2σ₊-σ₋-σ̄₋)/(4η²)`, where

* `ℓ_* = (-σ₊B_* + bd_*as)/(1+k₋s)`, `r = k₋ℓ_* - bd_*a`;
* `C₀ = bd_*² - b²d_*(aℓ_* + āℓ̄_*)`, `ℓ₁₂ = (d_*C₀ - rB_* - r̄B̄_* + σ₊C_*)/b`;
* `r₁₂ = kℓ₁₂ + C₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexConjugate

/-- `B_* = ⟨R²R*⟩ = c₀(d_* + s)`. -/
def jetB (b E : ℝ) (s : ℂ) : ℂ := cZero b E * ((dStar b : ℂ) + s)

/-- `C_* = ⟨R²(R*)²⟩ = (s + s̄ + 2d_*)/(4η²)`. -/
def jetC (b E : ℝ) (s : ℂ) : ℂ := (s + conj s + 2 * (dStar b : ℂ)) / (4 * (etaZ b E : ℂ) ^ 2)

/-- `ℓ_* = (-σ₊B_* + bd_*as)/(1+k₋s)`. -/
def ladderEll (b E : ℝ) (s : ℂ) : ℂ :=
  (-(sigmaPlus b : ℂ) * jetB b E s + (b : ℂ) * dStar b * matchedA E * s) / (1 + kMinus b E * s)

/-- `r = k₋ℓ_* - bd_*a`. -/
def ladderRStep (b E : ℝ) (s : ℂ) : ℂ :=
  kMinus b E * ladderEll b E s - (b : ℂ) * dStar b * matchedA E

/-- `C₀ = bd_*² - b²d_*(aℓ_* + āℓ̄_*)`. -/
def ladderC0 (b E : ℝ) (s : ℂ) : ℂ :=
  (b : ℂ) * (dStar b : ℂ) ^ 2 - (b : ℂ) ^ 2 * dStar b *
    (matchedA E * ladderEll b E s + conj (matchedA E) * conj (ladderEll b E s))

/-- `ℓ₁₂ = (d_*C₀ - rB_* - r̄B̄_* + σ₊C_*)/b`. -/
def ladderEll12 (b E : ℝ) (s : ℂ) : ℂ :=
  ((dStar b : ℂ) * ladderC0 b E s - ladderRStep b E s * jetB b E s -
      conj (ladderRStep b E s) * conj (jetB b E s) + (sigmaPlus b : ℂ) * jetC b E s) / b

/-- `r₁₂ = kℓ₁₂ + C₀`. -/
def ladderR12Step (b E : ℝ) (s : ℂ) : ℂ := (kPlus b : ℂ) * ladderEll12 b E s + ladderC0 b E s

section

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
include hb0 hb h1 h2

theorem one_sub_matchedA_sq_ne : 1 - matchedA E ^ 2 ≠ 0 := by
  intro h
  have hA := matchedA_ne_zero E h1 h2
  have hc := cZero_mul_conj_sub hb0 hb h1 h2
  rw [matchedA_inv E h1 h2 |>.symm] at hc
  have : (matchedA E)⁻¹ - matchedA E = 0 := by
    have : (matchedA E)⁻¹ - matchedA E = (1 - matchedA E ^ 2) / matchedA E := by
      field_simp
    rw [this, h, zero_div]
  rw [this, mul_zero] at hc
  have hd : (dStar b : ℂ) ≠ 0 := by
    have : dStar b ≠ 0 := by rw [dStar]; have : 0 < 1 - b := by linarith
                             positivity
    exact_mod_cast this
  exact hd hc.symm

/-- `c₀ = d_*a/(1-a²)`. -/
theorem cZero_eq_matched : cZero b E = (dStar b : ℂ) * matchedA E / (1 - matchedA E ^ 2) := by
  have hA := matchedA_ne_zero E h1 h2
  have hA2 := one_sub_matchedA_sq_ne hb0 hb h1 h2
  have hc := cZero_mul_conj_sub hb0 hb h1 h2
  rw [matchedA_inv E h1 h2 |>.symm] at hc
  rw [eq_div_iff hA2, ← hc]
  field_simp

omit hb0 hb h1 h2 in
theorem dStar_cast : (dStar b : ℂ) = 1 / (1 - (b : ℂ)) := by
  rw [dStar]; push_cast; rfl

omit hb0 hb h1 h2 in
theorem sigmaPlus_cast : (sigmaPlus b : ℂ) = ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2) / b := by
  rw [sigmaPlus, kPlus]; push_cast; rfl

omit hb0 hb h1 h2 in
theorem kMinus_cast : kMinus b E = (1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * matchedA E ^ 2 := by
  rw [kMinus]; push_cast; rfl

/-- **`r = c₀(σ₋ - σ₊)`** (first replica identity). -/
theorem ladderRStep_eq (s : ℂ) (hu : 1 + kMinus b E * s ≠ 0) :
    ladderRStep b E s = ladderR b E s := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hb1 : 1 - (b : ℂ) ≠ 0 := by
    have : (1 - b : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have hA2 := one_sub_matchedA_sq_ne hb0 hb h1 h2
  rw [kMinus_cast] at hu
  have key := step5_r (b : ℂ) (matchedA E) s hb' hb1 hA2 hu
  rw [ladderRStep, ladderR, ladderEll, jetB, sigmaMinus, cZero_eq_matched hb0 hb h1 h2,
    dStar_cast, sigmaPlus_cast, kMinus_cast]
  linear_combination key

/-- **`r₁₂ = (2σ₊-σ₋-σ̄₋)/(4η²)`** (second replica identity). -/
theorem ladderR12Step_eq (s : ℂ) (hu : 1 + kMinus b E * s ≠ 0) :
    ladderR12Step b E s = ladderR12 b E s := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hb1 : 1 - (b : ℂ) ≠ 0 := by
    have : (1 - b : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have hA := matchedA_ne_zero E h1 h2
  have hA2 := one_sub_matchedA_sq_ne hb0 hb h1 h2
  have hAi : conj (matchedA E) = (matchedA E)⁻¹ := (matchedA_inv E h1 h2).symm
  have hAi2 : 1 - (matchedA E)⁻¹ ^ 2 ≠ 0 := by
    intro h; apply hA2
    have : matchedA E ^ 2 = 1 := by field_simp at h; linear_combination h
    rw [this]; ring
  have hη : etaZ b E ≠ 0 := (etaZ_pos b E (by linarith) h1 h2).ne'
  set A := matchedA E
  set c0 := cZero b E
  set d : ℂ := (dStar b : ℂ)
  set sp : ℂ := (sigmaPlus b : ℂ)
  have hd : d = 1 / (1 - (b : ℂ)) := dStar_cast
  have hsp : sp = ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2) / b := sigmaPlus_cast
  have hc0 : c0 = d * A / (1 - A ^ 2) := cZero_eq_matched hb0 hb h1 h2
  have hc0' : -c0 = d * A⁻¹ / (1 - A⁻¹ ^ 2) := by
    rw [hc0]
    have h3 : A ^ 2 - 1 ≠ 0 := by intro h; apply hA2; linear_combination -h
    field_simp
    ring
  have hg : (4 * (etaZ b E : ℂ) ^ 2)⁻¹ = -c0 ^ 2 := by
    rw [cZero_sq b E hη]; push_cast; ring
  have hkm : kMinus b E = (1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * A ^ 2 := kMinus_cast
  have hkm' : conj (kMinus b E) = (1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * A⁻¹ ^ 2 := by
    rw [hkm]
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, Complex.conj_ofReal, hAi]
  have hu' : 1 + ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * A⁻¹ ^ 2) * conj s ≠ 0 := by
    rw [← hkm']
    have : 1 + conj (kMinus b E) * conj s = conj (1 + kMinus b E * s) := by simp
    rw [this]; exact (map_ne_zero _).mpr hu
  -- the `r` identity on both sheets
  have hr : ladderRStep b E s = c0 * (sigmaMinus b E s - sp) := by
    rw [ladderRStep_eq hb0 hb h1 h2 s hu, ladderR]
  have hr' : conj (ladderRStep b E s) = -c0 * (conj (sigmaMinus b E s) - sp) := by
    rw [hr, map_mul, map_sub, conj_cZero, Complex.conj_ofReal]
  -- closed forms of the conjugate sheet
  have hB' : conj (jetB b E s) = -c0 * (d + conj s) := by
    rw [jetB, map_mul, map_add, conj_cZero, Complex.conj_ofReal]
  have hell' : conj (ladderEll b E s) =
      (-sp * (-c0 * (d + conj s)) + b * d * A⁻¹ * conj s) /
        (1 + ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * A⁻¹ ^ 2) * conj s) := by
    rw [ladderEll, map_div₀, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_mul,
      map_neg, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal, map_one, hkm', hB',
      hAi]
  have hsm' : conj (sigmaMinus b E s) = ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * A⁻¹ ^ 2) /
      (1 + ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * A⁻¹ ^ 2) * conj s) := by
    rw [sigmaMinus, map_div₀, map_add, map_mul, map_one, hkm']
  -- the two sheets
  rw [hkm] at hu
  have F1 := step5_half (b : ℂ) A s hb' hb1 hA2 hu d sp (kMinus b E) c0 (ladderEll b E s)
    (sigmaMinus b E s) hd hsp hkm hc0 (by rw [ladderEll, jetB]) (by rw [sigmaMinus])
  have F2 := step5_half (b : ℂ) A⁻¹ (conj s) hb' hb1 hAi2 hu' d sp _ (-c0)
    (conj (ladderEll b E s)) (conj (sigmaMinus b E s)) hd hsp rfl hc0' hell' hsm'
  rw [neg_sq] at F2
  have Asm := step5_assembly (b : ℂ) d sp A A⁻¹ s (conj s) c0 (ladderEll b E s)
    (conj (ladderEll b E s)) (sigmaMinus b E s) (conj (sigmaMinus b E s)) (ladderRStep b E s)
    (conj (ladderRStep b E s)) hb' hb1 hd hsp hr hr'
  have hphi := step5_phi_antisymm d A hA hA2
  simp only at Asm
  have hC : jetC b E s = (-c0 ^ 2) * (s + conj s + 2 * d) := by
    rw [jetC, div_eq_mul_inv, hg]; ring
  rw [ladderR12Step, ladderEll12, ladderC0, hC, hB', kPlus, ladderR12,
    div_eq_mul_inv _ (4 * (etaZ b E : ℂ) ^ 2), hg]
  push_cast
  rw [hAi, show jetB b E s = c0 * ((dStar b : ℂ) + s) from rfl]
  linear_combination Asm + F1 + F2 + hphi

theorem ladderRStep_eq_of_jet {s : ℂ} (hs : IsStationaryJet b E s) :
    ladderRStep b E s = ladderR b E s := by
  refine ladderRStep_eq hb0 hb h1 h2 s fun h => ?_
  have := jet_denom_pos hb0 hb h1 h2 s hs.2
  rw [h, norm_zero] at this; linarith

theorem ladderR12Step_eq_of_jet {s : ℂ} (hs : IsStationaryJet b E s) :
    ladderR12Step b E s = ladderR12 b E s := by
  refine ladderR12Step_eq hb0 hb h1 h2 s fun h => ?_
  have := jet_denom_pos hb0 hb h1 h2 s hs.2
  rw [h, norm_zero] at this; linarith

end

end BlockBand.Transmission.PassiveCovariance
