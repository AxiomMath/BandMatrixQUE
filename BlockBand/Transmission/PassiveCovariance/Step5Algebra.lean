module

public import BlockBand.Prelude

/-!
# The replica scalar identities as rational identities

* `step5_r`: `k₋ℓ_* - bd_*A = c₀(σ₋ - σ₊)`, where
  `ℓ_* = (-σ₊c₀(d_*+S) + bd_*AS)/(1+k₋S)` and `σ₋ = k₋/(1+k₋S)`.
* `step5_half`: `F(A,S) = d_*²(1+A²)/(2(1-A²))` for every `S`. Here `F` is the one-sheet part
  of `r₁₂ - (2σ₊-σ₋-σ̄₋)/(4η²)`, and `1/(4η²) = -c₀²`.
* `step5_assembly`: `r₁₂ - γ(2σ₊-σ₋-σ̄₋) = F(A,S) + F(A',T)`, given the `r` identity on both
  sheets.
* `step5_phi_antisymm`: `φ(A) + φ(A⁻¹) = 0`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Transmission.PassiveCovariance

/-- **`r = c₀(σ₋ - σ₊)`** (first replica identity). -/
theorem step5_r (b A S : ℂ) (hb : b ≠ 0) (hb1 : 1 - b ≠ 0) (hA2 : 1 - A ^ 2 ≠ 0)
    (hu : 1 + ((1 - 2 * b) + b ^ 2 * A ^ 2) * S ≠ 0) :
    ((1 - 2 * b) + b ^ 2 * A ^ 2) *
        ((-(((1 - 2 * b) + b ^ 2) / b) * ((1 / (1 - b)) * A / (1 - A ^ 2) * (1 / (1 - b) + S)) +
          b * (1 / (1 - b)) * A * S) / (1 + ((1 - 2 * b) + b ^ 2 * A ^ 2) * S)) -
      b * (1 / (1 - b)) * A =
    (1 / (1 - b)) * A / (1 - A ^ 2) *
      (((1 - 2 * b) + b ^ 2 * A ^ 2) / (1 + ((1 - 2 * b) + b ^ 2 * A ^ 2) * S) -
        ((1 - 2 * b) + b ^ 2) / b) := by
  field_simp
  ring

/-- **One sheet of the second identity**: `F(A,S)` does not depend on `S`. -/
theorem step5_half (b A S : ℂ) (hb : b ≠ 0) (hb1 : 1 - b ≠ 0) (hA2 : 1 - A ^ 2 ≠ 0)
    (hu : 1 + ((1 - 2 * b) + b ^ 2 * A ^ 2) * S ≠ 0) (d sp km c0 ell sm : ℂ)
    (hd : d = 1 / (1 - b)) (hsp : sp = ((1 - 2 * b) + b ^ 2) / b)
    (hkm : km = (1 - 2 * b) + b ^ 2 * A ^ 2) (hc0 : c0 = d * A / (1 - A ^ 2))
    (hell : ell = (-sp * (c0 * (d + S)) + b * d * A * S) / (1 + km * S))
    (hsm : sm = km / (1 + km * S)) :
    d ^ 2 / 2 - b * d * A * ell + sp * (-c0 ^ 2) * sm * (d + S) - (-c0 ^ 2) * (sp - sm) =
      d ^ 2 * (1 + A ^ 2) / (2 * (1 - A ^ 2)) := by
  rw [← hkm] at hu
  have hu' : 1 + S * km ≠ 0 := by rwa [mul_comm]
  rw [hell, hsm, hc0, hsp, hd]
  field_simp
  rw [hkm]
  ring

/-- **Assembly of the second identity** from the `r` identity on both sheets (`γ = -c₀²`). -/
theorem step5_assembly (b d sp A A' S T c0 ell ell' sm sm' r r' : ℂ) (hb : b ≠ 0)
    (hb1 : 1 - b ≠ 0) (hd : d = 1 / (1 - b)) (hsp : sp = ((1 - 2 * b) + b ^ 2) / b)
    (hr : r = c0 * (sm - sp)) (hr' : r' = -c0 * (sm' - sp)) :
    let B := c0 * (d + S)
    let B' := -c0 * (d + T)
    let C0 := b * d ^ 2 - b ^ 2 * d * (A * ell + A' * ell')
    let Cs := (-c0 ^ 2) * (S + T + 2 * d)
    ((1 - 2 * b) + b ^ 2) * ((d * C0 - r * B - r' * B' + sp * Cs) / b) + C0 -
        (-c0 ^ 2) * (2 * sp - sm - sm') =
      (d ^ 2 / 2 - b * d * A * ell + sp * (-c0 ^ 2) * sm * (d + S) - (-c0 ^ 2) * (sp - sm)) +
        (d ^ 2 / 2 - b * d * A' * ell' + sp * (-c0 ^ 2) * sm' * (d + T) -
          (-c0 ^ 2) * (sp - sm')) := by
  intro B B' C0 Cs
  simp only [B, B', C0, Cs]
  rw [hr, hr', hsp, hd]
  field_simp
  ring

/-- `φ(A) + φ(A⁻¹) = 0` for `φ(A) = d²(1+A²)/(2(1-A²))`. -/
theorem step5_phi_antisymm (d A : ℂ) (hA : A ≠ 0) (hA2 : 1 - A ^ 2 ≠ 0) :
    d ^ 2 * (1 + A ^ 2) / (2 * (1 - A ^ 2)) + d ^ 2 * (1 + A⁻¹ ^ 2) / (2 * (1 - A⁻¹ ^ 2)) =
      0 := by
  have h2 : 1 - A⁻¹ ^ 2 ≠ 0 := by
    intro h
    apply hA2
    have : A ^ 2 = 1 := by
      field_simp at h
      linear_combination h
    rw [this]; ring
  have h3 : A ^ 2 - 1 ≠ 0 := by
    intro h; apply hA2; linear_combination -h
  field_simp
  ring

end BlockBand.Transmission.PassiveCovariance
